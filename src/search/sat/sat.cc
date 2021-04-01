#include "sat.h"
#include <iostream>
#include <unordered_map>

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

/* Using two 2D vectors to store the state variables (facts) for the current and
       following time step.
       TODO: Find a way to indicate which vector represents the current/following
       state variables. It will alternate each timestep, since t+1 will become t in
       the following iteration. And the contents of the former current state will be
       replaced with the variables for the following time step. Pointers? Bool flag?
*/
vector<vector<int>> factsAtTnow;
vector<vector<int>> factsAtTplusOne;

/* Using a 2D vector to store the operator variables for each time step.
   Each vector represents the time step at which an operator was executed
   (if true in the returned plan).
*/
vector<vector<int>> operatorVars;

int timeStep = 0;

void sat_init(TaskProxy task_proxy, sat_capsule & capsule) {
    // Initially fill the corresponding vectors with the variables representing
    // the initial state and the following time step.
    for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
        vector<int> mutexGroupNow;
        vector<int> mutexGroupPlusOne;
        for (int j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
            mutexGroupNow.push_back(capsule.new_variable());
            mutexGroupPlusOne.push_back(capsule.new_variable());
        }
        factsAtTnow.push_back(mutexGroupNow);
        factsAtTplusOne.push_back(mutexGroupPlusOne);
    }

    // Initially fill the vector with the variables representing which operator
    // was executed (if true in the returned plan) at t0.
    vector<int> operatorsAtTnow;
    for (size_t i=0; i<task_proxy.get_operators().size(); i++) {
        operatorsAtTnow.push_back(capsule.new_variable());
    }
    operatorVars.push_back(operatorsAtTnow);

    /* <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@> <@=*=@
    FactsProxyIterator fact_it = task_proxy.get_variables().get_facts().end();
    cout << AbstractTask(task_proxy).get_variable_name(1) << endl;
    cout << task_proxy.get_variables().size() << endl; ---this works!
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
    VariableProxy vp = task_proxy.get_variables()[2];
    cout << "There are " << task_proxy.get_variables().size() << " variables." << endl;
    cout << "Output: " << task_proxy.get_operators()[0].get_effects()[0].get_fact().get_name() << endl;
    for (int n=0; n<9; n++) {
        FactProxy fp1 = task_proxy.get_goals()[n];
        cout << "Fact name is: " << fp1.get_name() << endl;
        for (int o=0; o<2; o++) {
            FactProxy fp = vp.get_fact(o);
            cout << "Fact name is: " << fp.get_name() << " and has value: " << fp.get_value() << endl;
        }
    }
    FactProxy fp = vp.get_fact(0);
    for (int n=0; n<10; n++) {
        cout << vp.get_fact(n).get_pair() << endl;
    }
    FactPair fpair = fp.get_pair();
    cout << fpair << endl;
    cout << fp.get_value() << " and has name: " << fp.get_name() << endl;
    cout << vp.get_domain_size() << endl; --- this works!
    FactsProxyIterator fpi_begin = task_proxy.get_variables().get_facts().begin();
    FactsProxyIterator fpi_end = task_proxy.get_variables().get_facts().end();
    AbstractTask abs_task(tasks::g_root_task); geht nicht wegen Funktionen */
}

void* solver = ipasir_init();

void sat_encoding(TaskProxy task_proxy, sat_capsule & capsule) {
    // Add the variables reflecting the goal state of the problem.
    for (size_t i=0; i<task_proxy.get_goals().size(); i++) {
        assertYes(solver, factsAtTplusOne[task_proxy.get_goals()[i].get_pair().var][task_proxy.get_goals()[i].get_pair().value]);
    }
    // Add the variables reflecting the initial state of the problem.
    for (size_t i=0; i<factsAtTnow.size(); i++) {
        for (size_t j=0; j<factsAtTnow[i].size(); j++) {
            if (task_proxy.get_initial_state().get_values()[i] == j) {
                assertYes(solver, factsAtTnow[i][j]);
            } else {
                assertNot(solver, factsAtTnow[i][j]);
            }
        }
    }
    // Add clauses reflecting the mutex condition of a group of variables.
    for (size_t i=0; i<factsAtTplusOne.size(); i++) {
        atLeastOne(solver, capsule, factsAtTplusOne[i]);
        atMostOne(solver, capsule, factsAtTplusOne[i]);
    }
    // Vector to collect frame actions executing the same effects.
    vector<vector<vector<int>>> frameAxioms;
    for (int i=0; i<task_proxy.get_variables().size(); i++) {
        vector<vector<int>> variable;
        for (int j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
            vector<int> fact;
            variable.push_back(fact);
        }
    frameAxioms.push_back(variable);
    }
    // Add clauses reflecting the operators at the current time step.
    for (OperatorProxy const & operators : task_proxy.get_operators()) {
        int operatorVar = operatorVars[timeStep][operators.get_id()];
        for (FactProxy const & preconditions : operators.get_preconditions()) {
            implies(solver, operatorVar, factsAtTnow[preconditions.get_pair().var][preconditions.get_pair().value]);
        }
        for (EffectProxy const & effects : operators.get_effects()) {
            int effectVar = factsAtTplusOne[effects.get_fact().get_pair().var][effects.get_fact().get_pair().value];
            implies(solver, operatorVar, effectVar);
            // Add frame axiom for the rising flank (neg state becomes pos state)
            frameAxioms[effects.get_fact().get_pair().var][effects.get_fact().get_value()].push_back(operatorVars[timeStep][operators.get_id()]);
        }
    }
    // Add frame axiom clauses.
    for (int i=0; i<frameAxioms.size(); i++) {
        for (int j=0; j<frameAxioms[i].size(); j++) {
            int neg = factsAtTnow[i][j];
            int pos = factsAtTplusOne[i][j];
            impliesPosAndNegImpliesOr(solver, neg, pos, frameAxioms[i][j]);
        }
    }
    // Add clauses such that exactly one operator can be picked per time step.
    atLeastOne(solver, capsule, operatorVars[timeStep]);
    atMostOne(solver, capsule, operatorVars[timeStep]);
    cout << "That many clauses have been added: " << get_number_of_clauses() << endl;
    cout << ipasir_solve(solver) << endl;
    /*int clause = capsule.number_of_variables;
    if (ipasir_solve(solver) == 10){
        for (int v = 1; v <= clause; v++)
            for (int i=0; i<operatorVars[timeStep].size(); i++) {
                if (operatorVars[timeStep][i] == v) cout  << "V " << v << ": " << ipasir_val(solver,v) << endl;
            }
    }*/
}

}