#include "command_line.h"
#include "ipasir.h"
#include "option_parser.h"
#include "search_engine.h"

#include "options/registries.h"
#include "tasks/root_task.h"
#include "task_utils/task_properties.h"
#include "../utils/logging.h"
#include "utils/system.h"
#include "utils/timer.h"

#include <iostream>

using namespace std;
using utils::ExitCode;

// <@=*=@> Function from Gregor to test IPASIR interface <@=*=@>
void sat_solver_call(){
     cout << ipasir_signature() << endl;
     void* solver = ipasir_init();
     ipasir_add(solver,-1);
     ipasir_add(solver,-2);
     ipasir_add(solver,0);

     ipasir_add(solver,-3);
     ipasir_add(solver,2);
     ipasir_add(solver,0);

     ipasir_add(solver,3);
     ipasir_add(solver,0);

     int state = ipasir_solve(solver);
     cout << state << endl;
     if (state == 10){
         for (int v = 1; v <= 3; v++)
             cout  << "V " << v << ": " << ipasir_val(solver,v) << endl;
    }
}
// <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@>

int main(int argc, const char **argv) {
    // <@=*=@> sat_solver_call();
    // <@=*=@> return(0);
    utils::register_event_handlers();

    if (argc < 2) {
        utils::g_log << usage(argv[0]) << endl;
        utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
    }

    bool unit_cost = false;
    if (static_cast<string>(argv[1]) != "--help") {
        utils::g_log << "reading input..." << endl;
        tasks::read_root_task(cin);
        utils::g_log << "done reading input!" << endl;
        TaskProxy task_proxy(*tasks::g_root_task);
        unit_cost = task_properties::is_unit_cost(task_proxy);
        // <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@
        //FactsProxyIterator fact_it = task_proxy.get_variables().get_facts().end();
        //cout << AbstractTask(task_proxy).get_variable_name(1) << endl;
        // cout << task_proxy.get_variables().size() << endl; ---this works!
		cout << "There are that many initial values: " << task_proxy.get_initial_state().size() << endl;
		cout << "The initial Values are:" << endl;
		cout << task_proxy.get_initial_state().get_values() << endl;
		cout << "Name of variable 18 is: " << task_proxy.get_initial_state()[18].get_name() << endl;
		cout << "And it's FactPair looks like this: " << task_proxy.get_initial_state()[18].get_pair() << endl;
		cout << "There are that many goals: " << task_proxy.get_goals().size() << endl;
		cout << "The goal states are: " << endl;
		for (std::size_t i=0; i<task_proxy.get_goals().size(); i++) {
			cout << "Goal " << i+1 << ": " << task_proxy.get_goals()[i].get_name() << " is denoted as " << task_proxy.get_goals()[i].get_pair() << endl;
		}
		for (int i=0; i<21; i++) {
		    cout << "Variable " << task_proxy.get_variables()[i].get_name() << ": Has " << task_proxy.get_variables()[i].get_domain_size() << " items." << endl;
			for (int j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
				cout << "Item " << j << " is: " << task_proxy.get_variables()[i].get_fact(j).get_name() << endl;
			}
		}
		cout << "There are " << task_proxy.get_operators().size() << " operators." << endl;
		cout << "Operator 83 is called: " << task_proxy.get_operators()[82].get_name() << endl;
		cout << "Operator 83 preconditions are:" << endl;
		for (std::size_t i=0; i<task_proxy.get_operators()[82].get_preconditions().size(); i++) {
			cout << task_proxy.get_operators()[82].get_preconditions()[i].get_pair() << " is called " << task_proxy.get_operators()[82].get_preconditions()[i].get_name() << endl;
		}
		cout << "Operator 83 effects are:" << endl;
		for (std::size_t i=0; i<task_proxy.get_operators()[82].get_effects().size(); i++) {
			cout << task_proxy.get_operators()[82].get_effects()[i].get_fact().get_name() << endl;
			cout << "Precondition size is: " << task_proxy.get_operators()[82].get_effects()[i].get_conditions().size() << endl;
		}
		for (std::size_t o=0; o<task_proxy.get_operators().size(); o++) {
			cout << "Operator " << o+1 << " is: " << task_proxy.get_operators()[o].get_name() << endl;
		}
        for (OperatorProxy const & operators : task_proxy.get_operators()) {
            cout << operators.get_name() << " ... " << operators.get_id() << endl;
            cout << "Preconditions are: ";
            for (FactProxy const & preconditions : operators.get_preconditions()) {
                cout << preconditions.get_name() << " and ";
            }
            cout << endl;
        }
        for (VariableProxy const & variables : task_proxy.get_variables()) {
            cout << variables.get_name() << endl;
        }
		//VariableProxy vp = task_proxy.get_variables()[2];
		//cout << "There are " << task_proxy.get_variables().size() << " variables." << endl;
		//cout << "Output: " << task_proxy.get_operators()[0].get_effects()[0].get_fact().get_name() << endl;
		/*for (int n=0; n<9; n++) {
			FactProxy fp1 = task_proxy.get_goals()[n];
			cout << "Fact name is: " << fp1.get_name() << endl;
			for (int o=0; o<2; o++) {
				FactProxy fp = vp.get_fact(o);
				cout << "Fact name is: " << fp.get_name() << " and has value: " << fp.get_value() << endl;
			}
		} */
		//FactProxy fp = vp.get_fact(0);
		//for (int n=0; n<10; n++) {
		//	cout << vp.get_fact(n).get_pair() << endl;
		//}
		//FactPair fpair = fp.get_pair();
		//cout << fpair << endl;
		//cout << fp.get_value() << " and has name: " << fp.get_name() << endl;
		//cout << vp.get_domain_size() << endl; --- this works!
        //FactsProxyIterator fpi_begin = task_proxy.get_variables().get_facts().begin();
        //FactsProxyIterator fpi_end = task_proxy.get_variables().get_facts().end();
        //AbstractTask abs_task(tasks::g_root_task); geht nicht wegen Funktionen
        
    }

    // <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@>
    
    //FactProxy     
    //cout << FactProxy << endl;
    return(0);
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
