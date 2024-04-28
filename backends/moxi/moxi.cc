#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include <algorithm>
#include <string>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

enum MoxiVarType : unsigned char { INPUT = 0, OUTPUT = 1, LOCAL = 2 };

struct MoxiVar {
	std::string name;
	MoxiVarType var_type;
	std::string sort;

	MoxiVar() : name(""), var_type(LOCAL), sort("") {}
	MoxiVar(const std::string &name, MoxiVarType var_type, const std::string &sort) : name(name), var_type(var_type), sort(sort) {}
};

struct MoxiWorker {
	SigMap sigmap;
	RTLIL::Module *module;
	std::ostream &f;
	bool verbose;

	// Maps Wire names to MoXI variables
	dict<RTLIL::IdString, MoxiVar> var_map;

	std::vector<std::string> init_exprs, trans_exprs, inv_exprs, subsystems;
	dict<std::string, std::string> reach_exprs, fair_exprs, assume_exprs, current_exprs;

	MoxiWorker(RTLIL::Module *module, bool verbose, std::ostream &f) : sigmap(module), module(module), f(f), verbose(verbose) {}

	// Returns the MoXI variable name for `sig`
	std::string get_moxi_var_name(RTLIL::SigSpec &sig)
	{
		RTLIL::IdString sig_name = sig.as_wire()->name;
		if (var_map.find(sig_name) == var_map.end()) {
			// error?
		}
		return var_map[sig_name].name;
	}

	// Returns a string in MoXI syntax representing `sig` as a bool
	std::string get_moxi_bool(RTLIL::SigSpec &sig)
	{
		sigmap.apply(sig);

		if (sig.empty()) {
			// error
		} else if (sig.size() > 1) {
			// warn
		}

		if (sig.is_wire()) {
			std::string var_name = get_moxi_var_name(sig);
			return stringf("(= ((_ extract 0 0) %s) #b1)", var_name.c_str());
		}

		RTLIL::SigBit bit = sig[0];
		return bit.data == RTLIL::S1 ? "true" : "false";
	}

	// Returns a string in MoXI syntax representing `sig` as a bit vector. If `sig` is a wire, then
	// does a lookup of `sig` in `var_map`, otherwise builds a string using `sig`s chunks that
	// concats each chunk together.
	std::string get_moxi_bitvec(RTLIL::SigSpec &sig)
	{
		sigmap.apply(sig);

		if (sig.is_wire()) 
		{
			return get_moxi_var_name(sig);
		}

		std::vector<std::string> exprs;
		for (auto &chunk : sig.chunks()) 
		{
			if (chunk.is_wire()) 
			{
				exprs.push_back(get_moxi_var_name(sig));
				continue;
			}

			std::string bitvec = "#b";
			for (auto state = chunk.data.rbegin(); state != chunk.data.rend(); ++state) 
			{
				bitvec += (*state == RTLIL::S1) ? "1" : "0";
			}
			exprs.push_back(bitvec);
		}

		if (GetSize(exprs) == 0)
		{
			log_error("%s has no chunks.\n", sig.as_string().c_str());
			return "ERROR";
		}
		if (GetSize(exprs) == 1)
		{
			return exprs[0];
		}

		std::string moxi_bitvec = exprs.back();
		for (auto expr = ++(exprs.rbegin()); expr != exprs.rend(); ++expr)
		{
			moxi_bitvec = stringf("(concat %s %s)", moxi_bitvec.c_str(), (*expr).c_str());
		}

		return moxi_bitvec;
	}

	void run()
	{
		log("Running MoxiWorker on %s.\n", log_id(module->name));

		for (auto wire : module->wires()) {
			// FIXME: if a wire is both input + output, then just make it an input for now
			MoxiVarType var_type;
			if (wire->port_input) {
				var_type = INPUT;
			} else if (wire->port_output) {
				var_type = OUTPUT;
			} else {
				var_type = LOCAL;
			}

			std::string var_name = stringf("|%s|", log_id(wire->name));
			std::replace(var_name.begin(), var_name.end(), '\\', '/');

			var_map.emplace(wire->name, MoxiVar(var_name, var_type, stringf("(_ BitVec %d)", wire->width)));

			if (wire->attributes.count(ID::init)) {
				init_exprs.push_back(stringf("(= %s #b%s)", var_name.c_str(), wire->attributes.at(ID::init).as_string().c_str()));
			}
		}

		for (auto cell : module->cells()) {
			// FIXME: $slice, $concat, $mem

			if (cell->type.in(ID($assert), ID($cover), ID($assume), ID($fair))) {
				RTLIL::SigSpec sig_en = cell->getPort(ID::EN);
				RTLIL::SigSpec sig_a = cell->getPort(ID::A);

				std::string prop_name = stringf("|%s|", log_id(cell->name));
				std::replace(prop_name.begin(), prop_name.end(), '\\', '/');

				if (cell->type == ID($assert)) 
					reach_exprs[prop_name] = stringf("(and %s (not %s))", get_moxi_bool(sig_en).c_str(), get_moxi_bool(sig_a).c_str());
				else if (cell->type == ID($cover))
					reach_exprs[prop_name] = stringf("(and %s %s)", get_moxi_bool(sig_en).c_str(), get_moxi_bool(sig_a).c_str());
				else if (cell->type == ID($assume))
					assume_exprs[prop_name] = stringf("(and %s %s)", get_moxi_bool(sig_en).c_str(), get_moxi_bool(sig_a).c_str());
				else if (cell->type == ID($fair))
					fair_exprs[prop_name] = stringf("(and %s %s)", get_moxi_bool(sig_en).c_str(), get_moxi_bool(sig_a).c_str());

				continue;
			}

			if (cell->type.in(ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx))) {
				SigSpec sig_a = cell->getPort(ID::A);
				SigSpec sig_b = cell->getPort(ID::B);
				SigSpec sig_y = cell->getPort(ID::Y);

				continue;
			}

			if (cell->type.in(ID($not), ID($pos), ID($neg))) {
				// FIXME:

				continue;
			}

			if (cell->type.in(ID($add), ID($sub), ID($mul), ID($and), ID($or), ID($xor), ID($xnor))) {
				SigSpec sig_a = cell->getPort(ID::A);
				SigSpec sig_b = cell->getPort(ID::B);
				SigSpec sig_y = cell->getPort(ID::Y);

				string op;

				if (cell->type == ID($add))
					op = "bvadd";
				if (cell->type == ID($sub))
					op = "bvsub";
				if (cell->type == ID($mul))
					op = "bvmul";
				if (cell->type == ID($and))
					op = "bvand";
				if (cell->type == ID($or))
					op = "bvor";
				if (cell->type == ID($xor))
					op = "bvxor";
				if (cell->type == ID($xnor))
					op = "bvxnor";

				string expr = stringf("(= (%s %s %s) %s)", op.c_str(), get_moxi_bitvec(sig_a).c_str(), get_moxi_bitvec(sig_b).c_str(),
						      get_moxi_bitvec(sig_y).c_str());
				inv_exprs.push_back(expr);

				continue;
			}

			if (cell->type.in(ID($div), ID($mod), ID($modfloor))) {
				// FIXME:

				continue;
			}

			if (cell->type.in(ID($eq), ID($ne), ID($eqx), ID($nex), ID($lt), ID($le), ID($ge), ID($gt))) {
				SigSpec sig_a = cell->getPort(ID::A);
				SigSpec sig_b = cell->getPort(ID::B);
				SigSpec sig_y = cell->getPort(ID::Y);

				string op;

				// FIXME: signed v unsigned

				if (cell->type == ID($eq))
					op = "=";
				if (cell->type == ID($ne))
					op = "!=";
				if (cell->type == ID($eqx))
					op = "=";
				if (cell->type == ID($nex))
					op = "!=";
				if (cell->type == ID($lt))
					op = "bvult";
				if (cell->type == ID($le))
					op = "bvule";
				if (cell->type == ID($ge))
					op = "gvuge";
				if (cell->type == ID($gt))
					op = "bvgt";

				string expr = stringf("(= (%s %s %s) %s)", op.c_str(), get_moxi_bitvec(sig_a).c_str(), get_moxi_bitvec(sig_b).c_str(),
						      get_moxi_bitvec(sig_y).c_str());
				inv_exprs.push_back(expr);

				continue;
			}

			if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool))) {
				// FIXME:

				continue;
			}

			if (cell->type.in(ID($reduce_xor), ID($reduce_xnor))) {
				// FIXME:

				continue;
			}

			if (cell->type.in(ID($logic_and), ID($logic_or))) {
				// FIXME:

				continue;
			}

			if (cell->type.in(ID($logic_not))) {
				// FIXME:

				continue;
			}

			if (cell->type.in(ID($mux), ID($pmux))) {
				// FIXME:

				continue;
			}

			if (cell->type == ID($dff)) {
				// FIXME:
				SigSpec sig_d = cell->getPort(ID::D);
				SigSpec sig_q = cell->getPort(ID::Q);

				var_map.emplace(cell->name, MoxiVar(cell->name.str(), LOCAL, stringf("(_ BitVec %d)", GetSize(sig_d))));

				string expr = stringf("(= %s' %s)", get_moxi_bitvec(sig_q).c_str(), get_moxi_bitvec(sig_d).c_str());
				trans_exprs.push_back(expr);

				continue;
			}

			if (cell->type.in(ID($_BUF_), ID($_NOT_))) {
				// FIXME:

				continue;
			}

			if (cell->type.in(ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_), ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_))) {
				// FIXME:

				continue;
			}

			if (cell->type == ID($_MUX_)) {
				// FIXME:

				continue;
			}

			if (cell->type == ID($_NMUX_)) {
				// FIXME:

				continue;
			}

			if (cell->type == ID($_AOI3_)) {
				// FIXME:

				continue;
			}

			if (cell->type == ID($_OAI3_)) {
				// FIXME:

				continue;
			}

			if (cell->type == ID($_AOI4_)) {
				// FIXME:

				continue;
			}

			if (cell->type == ID($_OAI4_)) {
				// FIXME:

				continue;
			}

			if (cell->type[0] == '$') {
				if (cell->type.in(ID($dffe), ID($sdff), ID($sdffe), ID($sdffce)) || cell->type.str().substr(0, 6) == "$_SDFF" ||
				    (cell->type.str().substr(0, 6) == "$_DFFE" && cell->type.str().size() == 10)) {
					log_error("Unsupported cell type %s for cell %s.%s -- please run `dffunmap` before `write_moxi`.\n",
						  log_id(cell->type), log_id(module), log_id(cell));
				}
				if (cell->type.in(ID($adff), ID($adffe), ID($aldff), ID($aldffe), ID($dffsr), ID($dffsre)) ||
				    cell->type.str().substr(0, 5) == "$_DFF" || cell->type.str().substr(0, 7) == "$_ALDFF") {
					log_error("Unsupported cell type %s for cell %s.%s -- please run `async2sync; dffunmap` or `clk2fflogic` "
						  "before `write_moxi`.\n",
						  log_id(cell->type), log_id(module), log_id(cell));
				}
				if (cell->type.in(ID($sr), ID($dlatch), ID($adlatch), ID($dlatchsr)) || cell->type.str().substr(0, 8) == "$_DLATCH" ||
				    cell->type.str().substr(0, 5) == "$_SR_") {
					log_error("Unsupported cell type %s for cell %s.%s -- please run `clk2fflogic` before `write_moxi`.\n",
						  log_id(cell->type), log_id(module), log_id(cell));
				}
				log_error("Unsupported cell type %s for cell %s.%s.\n", log_id(cell->type), log_id(module), log_id(cell));
			}

			for (auto &conn : cell->connections()) {
			}
		}

		f << stringf("(define-system %s\n", module->name.c_str());

		f << stringf(":input (");
		for (auto it : var_map) {
			MoxiVar var = it.second;
			if (var.var_type != INPUT)
				continue;
			f << stringf("(%s %s) ", var.name.c_str(), var.sort.c_str());
		}
		f << stringf(")\n");

		f << stringf(":output (");
		for (auto it : var_map) {
			MoxiVar var = it.second;
			if (var.var_type != OUTPUT)
				continue;
			f << stringf("(%s %s) ", var.name.c_str(), var.sort.c_str());
		}
		f << stringf(")\n");

		f << stringf(":local (");
		for (auto it : var_map) {
			MoxiVar var = it.second;
			if (var.var_type != LOCAL)
				continue;
			f << stringf("(%s %s) ", var.name.c_str(), var.sort.c_str());
		}
		f << stringf(")\n");

		if (!init_exprs.empty()) {
			f << stringf(":init (\n");
			for (auto expr : init_exprs) {
				f << "\t" << expr << "\n";
			}
			f << stringf(")\n");
		}

		if (!trans_exprs.empty()) {
			f << stringf(":trans (\n");
			for (auto expr : trans_exprs) {
				f << "\t" << expr << "\n";
			}
			f << stringf(")\n");
		}

		if (!inv_exprs.empty()) {
			f << stringf(":inv (\n");
			for (auto expr : inv_exprs) {
				f << "\t" << expr << "\n";
			}
			f << stringf(")\n");
		}

		f << stringf(")\n"); // end define-system

		f << stringf("(check-system %s\n", module->name.c_str());

		f << stringf(":input (");
		for (auto it : var_map) {
			MoxiVar var = it.second;
			if (var.var_type != INPUT)
				continue;
			f << stringf("(%s %s) ", var.name.c_str(), var.sort.c_str());
		}
		f << stringf(")\n");

		f << stringf(":output (");
		for (auto it : var_map) {
			MoxiVar var = it.second;
			if (var.var_type != OUTPUT)
				continue;
			f << stringf("(%s %s) ", var.name.c_str(), var.sort.c_str());
		}
		f << stringf(")\n");

		f << stringf(":local (");
		for (auto it : var_map) {
			MoxiVar var = it.second;
			if (var.var_type != LOCAL)
				continue;
			f << stringf("(%s %s) ", var.name.c_str(), var.sort.c_str());
		}
		f << stringf(")\n");

		if (!reach_exprs.empty()) {
			f << stringf(":reach (\n");
			for (auto expr : reach_exprs) {
				f << "\t" << stringf("(%s %s)", expr.first.c_str(), expr.second.c_str()) << "\n";
			}
			f << stringf(")\n");

			f << stringf(":query (\n");
			for (auto expr : reach_exprs) {
				f << "\t" << stringf("(%s %s)", expr.first.c_str(), expr.first.c_str()) << "\n";
			}
			f << stringf(")\n");
		}

		f << stringf(")\n"); // end check-system
	}
};

struct MoxiBackend : public Backend {
	MoxiBackend() : Backend("moxi", "write design to MoXI file") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_moxi [filename]\n");
		log("\n");
		log("Write an MoXI description of the current design.\n");
		log("THIS COMMAND IS UNDER CONSTRUCTION\n");
		log("\n");
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool verbose = false;

		log_header(design, "Executing MoXI backend.\n");

		log_push();
		Pass::call(design, "bmuxmap");
		Pass::call(design, "demuxmap");
		Pass::call(design, "bwmuxmap");
		log_pop();

		extra_args(f, filename, args, 1);

		pool<Module *> modules;

		for (auto module : design->modules()) {
			if (!module->get_blackbox_attribute() && !module->has_memories_warn() && !module->has_processes_warn())
				modules.insert(module);
		}

		if (!modules.empty()) {
			*f << stringf("; MoXI description generated by %s\n", yosys_version_str);

			for (auto module : modules) {
				log("Creating MoXI representation of module %s.\n", log_id(module));
				MoxiWorker worker(module, verbose, *f);
				worker.run();
			}

			*f << stringf("; end of yosys output\n");
		}
	}
} MoxiBackend;

PRIVATE_NAMESPACE_END
