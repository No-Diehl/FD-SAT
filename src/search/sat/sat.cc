#include "sat.h"
#include <iostream>
#include<unordered_map>

using namespace std;

namespace sat {
// <@=*=@> Function from Gregor to test IPASIR interface <@=*=@>
void sat_solver_call() {
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


void sat_init(TaskProxy task_proxy) {
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
			cout << "Item " << j << " is: " << task_proxy.get_variables()[i].get_fact(j).get_name() <<
				" coded as " << task_proxy.get_variables()[i].get_fact(j).get_pair() << endl;
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

void sat_encoding(TaskProxy task_proxy, sat_capsule & capsule) {
    
    /* Store State (facts) and Action Variables in respective 2D vectors. The position of
       the variables inside the vector corresponds to the time step in which they are true
       (states) or can be executed (actions). */
    unordered_map<string, vector<int>> statesAtTimepoints;
    unordered_map<string, vector<int>> actionsAtTimepoints;
    int numOfVariables = 0;

    /* Using two 2D vectors to store the state variables (facts) for the current and
       following time step.
       TODO: Use pointers to indicate which vector represents the current/following
       state variables. It will alternate each timestep, since t+1 will become t in
       the following iteration. And the contents of the former current state will be
       replaced with the variables for the following time step.
    */
    vector<vector<int>> factsAtTnow;
    vector<vector<int>> factsAtTplusOne;
    for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
        vector<int> mutexGroupNow;
        vector<int> mutexGroupPlusOne;
        for (size_t j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
            mutexGroupNow.push_back(capsule.new_variable());
            mutexGroupPlusOne.push_back(capsule.new_variable());
        }
        factsAtTnow.push_back(mutexGroupNow);
        factsAtTplusOne.push_back(mutexGroupPlusOne);
    }

    /* Using a 2D vector to store the operator variables for each time step.
       Each vector represents the time step at which an operator was executed
       (if true in the returned plan).
    */
	vector<vector<int>> operatorVars;
    vector<int> operatorsAtTnow;
    for (OperatorProxy const & operators : task_proxy.get_operators()) {
        operatorsAtTnow.push_back(capsule.new_variable());
    }
    operatorVars.push_back(operatorsAtTnow);
    operatorsAtTnow.clear();
	
    for (int i=0; i<task_proxy.get_variables().size(); i++) {
		for (int j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
			statesAtTimepoints[task_proxy.get_variables()[i].get_fact(j).get_name()].push_back(++numOfVariables);
		}
	}
	/*for (auto & map : statesAtTimepoints) {
		cout << map.first << " has values " << map.second << endl;
	}*/

	for (OperatorProxy const & operators : task_proxy.get_operators()) {
		actionsAtTimepoints[operators.get_name()].push_back(++numOfVariables);
	}

	/*for (auto & map : actionsAtTimepoints) {
		cout << map.first << " has values " << map.second << endl;
	}*/
}

}