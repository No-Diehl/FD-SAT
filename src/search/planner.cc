#include "command_line.h"
#include "ipasir.h"
#include "option_parser.h"
#include "search_engine.h"
#include "sat/sat.h"
#include "sat_encoder.h"

#include "options/registries.h"
#include "tasks/root_task.h"
#include "task_utils/task_properties.h"
#include "../utils/logging.h"
#include "utils/system.h"
#include "utils/timer.h"

#include <iostream>

using namespace std;
using utils::ExitCode;

int main(int argc, const char **argv) {
    // cout << ipasir_signature() << endl;
    utils::register_event_handlers();

    if (argc < 2) {
        utils::g_log << usage(argv[0]) << endl;
        utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
    }

    // Explaining my custom search options.
    string search_option = argv[2];
    if (search_option == "help") {
        cout << "The following options can be used for SAT search:" << endl;
        cout << "\t normal\t\t\t direct encoding only" << endl;
        cout << "\t binary\t\t\t binary encoding only" << endl;
        cout << "\t invariants\t\t direct encoding + invariants (if present)" << endl;
        cout << "\t bin-invariants\t\t binary encoding + invariants (if present)" << endl;
        cout << "\t inv-forall\t\t direct encoding + invariants (if present) + forall step" << endl;
        cout << "\t bin-inv-forall\t\t binary encoding + invariants (if present) + forall step" << endl;
        cout << "\t forall\t\t\t direct encoding + forall step" << endl;
        cout << "\t bin-forall\t\t binary encoding + forall step" << endl;
        utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
    }

    bool unit_cost = false;
    if (static_cast<string>(argv[1]) != "--help") {
        utils::g_log << "reading input..." << endl;
        tasks::read_root_task(cin);
        utils::g_log << "done reading input!" << endl;
        TaskProxy task_proxy(*tasks::g_root_task);
        unit_cost = task_properties::is_unit_cost(task_proxy);
        // Check, if there are conditional effects. If so, abort program.
        for (OperatorProxy const & operators : task_proxy.get_operators()) {
            for (EffectProxy const & effects : operators.get_effects()) {
                if (!effects.get_conditions().empty()) {
                    cout << "CONDITIONAL EFFECT FOUND! Conditional effects are not supported, "
                         << "exiting program." << endl;
                    utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
                }
            }
        }
        map<string, int> sat_options;
        sat_options["normal"] = 1;
        sat_options["binary"] = 2;
        sat_options["invariants"] = 3;
        sat_options["bin-invariants"] = 4;
        sat_options["inv-forall"] = 5;
        sat_options["bin-inv-forall"] = 6;
        sat_options["forall"] = 7;
        sat_options["bin-forall"] = 8;
        int so = sat_options[search_option];
        bool plan_found = false;
        int round = 1;
        while (!plan_found) {
            cout << "Encoding for max. " << round << " steps." << endl;
            // plan_found = sat::sat_encoding_binary(task_proxy, round);
            switch (so) {
                case 1:
                    plan_found = sat::sat_encoding(task_proxy, round, false, false);
                    break;
                case 2:
                    plan_found = sat::sat_encoding_binary(task_proxy, round, false, false);
                    break;
                case 3:
                    plan_found = sat::sat_encoding(task_proxy, round, true, false);
                    break;
                case 4:
                    plan_found = sat::sat_encoding_binary(task_proxy, round, true, false);
                    break;
                case 5:
                    plan_found = sat::sat_encoding(task_proxy, round, true, true);
                    break;
                case 6:
                    plan_found = sat::sat_encoding_binary(task_proxy, round, true, true);
                    break;
                case 7:
                    plan_found = sat::sat_encoding(task_proxy, round, false, true);
                    break;
                case 8:
                    plan_found = sat::sat_encoding_binary(task_proxy, round, false, true);
                    break;
            }
            // Trying a different iteration pattern.
            if (round < 32) {round *= 2;}
            else if (round < 364) {round = (int)(round*1.5);}
            else if (round < 1385) {round = (int)(round*1.25);}
            else if (round < 2805) {round = (int)(round*1.125);}
            else {round = (int)(round*1.065);}
        }         
    }

    // <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@>
    // End planner here for testing purposes.
    utils::g_timer.stop();
    utils::g_log << "Total time: " << utils::g_timer << endl;
    ExitCode exitcd = ExitCode::SUCCESS;
    utils::report_exit_code_reentrant(exitcd);
    return static_cast<int>(exitcd);
    // <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@>

    shared_ptr<SearchEngine> engine;

    // The command line is parsed twice: once in dry-run mode, to
    // check for simple input errors, and then in normal mode.
    try {
        options::Registry registry(*options::RawRegistry::instance());
        parse_cmd_line(argc, argv, registry, true, unit_cost);
        engine = parse_cmd_line(argc, argv, registry, false, unit_cost);
    } catch (const ArgError &error) {
        error.print();
        usage(argv[0]);
        utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
    } catch (const OptionParserError &error) {
        error.print();
        usage(argv[0]);
        utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
    } catch (const ParseError &error) {
        error.print();
        utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
    }

    utils::Timer search_timer;
    engine->search();
    search_timer.stop();
    utils::g_timer.stop();

    engine->save_plan_if_necessary();
    engine->print_statistics();
    utils::g_log << "Search time: " << search_timer << endl;
    utils::g_log << "Total time: " << utils::g_timer << endl;

    ExitCode exitcode = engine->found_solution()
        ? ExitCode::SUCCESS
        : ExitCode::SEARCH_UNSOLVED_INCOMPLETE;
    utils::report_exit_code_reentrant(exitcode);
    return static_cast<int>(exitcode);
}
