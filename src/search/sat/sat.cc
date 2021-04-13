#include "sat.h"
#include <unistd.h> // for directory path
#include <cstdlib> // for exit-function
#include <fstream> // for file generation
#include <iostream>


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
*/
vector<vector<int>> factsAtTnow;
vector<vector<int>> factsAtTplusOne;

/* Using a 2D vector to store the operator variables for each time step.
   Each vector represents the time step at which an operator was executed
   (if true in the returned plan).
*/
vector<vector<int>> operatorVars;

void* solver = ipasir_init();

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

/* Using two 3D vectors to store the state variables (facts) for the current and
   following time step.
*/
vector<vector<vector<int>>> binaryFactsAtTnow;
vector<vector<vector<int>>> binaryFactsAtTplusOne;

void forbidden_binary_states(vector<vector<vector<int>>> & binaryFacts) {
    for (auto i=0; i<binaryFacts.size(); i++) {
        if (binaryFacts[i].size()%2 != 0) {
            int bits = sizeof(int)*8-__builtin_clz(binaryFacts[i].size());
            int nxtPowOfTwo = 2;
            for (int i=1; i<bits; i++) {nxtPowOfTwo *= 2;}
            for (int j=binaryFacts[i].size(); j<nxtPowOfTwo; j++) {
                int count = 0;
                vector<int> forbiddenState;
                for (int k=binaryFacts[i][0].size()-1; k>=0; k--) {
                    if (j & (1 << k)) {
                        forbiddenState.push_back(binaryFacts[i][0][count]);
                        count++;
                    } else {
                        forbiddenState.push_back(-binaryFacts[i][0][count]);
                        count++;
                    }
                }
                assertOr(solver, forbiddenState);
            }
        }
    }
}

void sat_init_binary(TaskProxy task_proxy, sat_capsule & capsule) {
    for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
        vector<vector<int>> mutexGroupNow;
        vector<vector<int>> mutexGroupPlusOne;
        // Calculate number of needed variables to represent all facts of current mutex group.
        int binaryVars;
        /* 
        Differentiate between powers of 2 and other numbers. Group sizes of exact powers of 2
        need one bit less to represent all members.
        Note: __builtin_popcount(unsigned int x) returns the num of 1-bits in x
        */
        if (__builtin_popcount(task_proxy.get_variables()[i].get_domain_size()) == 1) {
            // Note: __builtin_ctz(unsigned int x) returns num of trailing 0-bits in x
            binaryVars = __builtin_ctz(task_proxy.get_variables()[i].get_domain_size());
        } else {
            // Note: __builtin_clz(unsigned int x) return the num of leading 0-bits in x
            binaryVars = sizeof(int)*8-__builtin_clz(task_proxy.get_variables()[i].get_domain_size());
        }
        // Vectors containing the template variables for a mutex group.
        vector<int> factBinaryVarsNow;
        vector<int> factBinaryVarsPlusOne;
        for (int j=0; j<binaryVars; j++) {
            factBinaryVarsNow.push_back(capsule.new_variable());
            factBinaryVarsPlusOne.push_back(capsule.new_variable());
        }
        // Push the binary fact encodings into a vector, a positive int representing a 1-bit
        // and a negative int representing a 0-bit using the registered template variables.
        for (int k=0; k<task_proxy.get_variables()[i].get_domain_size(); k++) {
            vector<int> factVarsStatesNow;
            vector<int> factVarsStatesPlusOne;
            for (int l=factBinaryVarsNow.size()-1; l>=0; l--) {
                if (k & (1 << l)) {
                    factVarsStatesNow.push_back(factBinaryVarsNow[factBinaryVarsNow.size()-1-l]);
                    factVarsStatesPlusOne.push_back(factBinaryVarsPlusOne[factBinaryVarsPlusOne.size()-1-l]);
                } else {
                    factVarsStatesNow.push_back(-factBinaryVarsNow[factBinaryVarsNow.size()-1-l]);
                    factVarsStatesPlusOne.push_back(-factBinaryVarsPlusOne[factBinaryVarsPlusOne.size()-1-l]);
                }
            }
            mutexGroupNow.push_back(factVarsStatesNow);
            mutexGroupPlusOne.push_back(factVarsStatesPlusOne);
        }
        binaryFactsAtTnow.push_back(mutexGroupNow);
        binaryFactsAtTplusOne.push_back(mutexGroupPlusOne);
    }
    //cout << "States at t0: " << binaryFactsAtTnow << endl;
    //cout << "States at t1: " << binaryFactsAtTplusOne << endl;

    // Find and add the unused binary states for the mutex groups.
    forbidden_binary_states(binaryFactsAtTnow);
    forbidden_binary_states(binaryFactsAtTplusOne);

    // Initially fill the vector with the variables representing which operator
    // was executed (if true in the returned plan) at t0.
    vector<int> operatorsAtTnow;
    for (size_t i=0; i<task_proxy.get_operators().size(); i++) {
        operatorsAtTnow.push_back(capsule.new_variable());
    }
    operatorVars.push_back(operatorsAtTnow);
    //cout << "Operators at t0: " << operatorVars << endl;
}

void sat_step(TaskProxy task_proxy, sat_capsule & capsule) {
    factsAtTnow.swap(factsAtTplusOne);
    // Replace all the variables in factsAtTplusOne with new variables for the current time step.
    for (size_t i=0; i<factsAtTplusOne.size(); i++) {
        for (size_t j=0; j<factsAtTplusOne[i].size(); j++) {
            factsAtTplusOne[i][j] = capsule.new_variable();
        }
    }

    // Create a new vector<int> with variables representing which operator was executed
    // (if true in the returned plan) at the current time step.
    vector<int> operatorsAtTnow;
    for (size_t i=0; i<task_proxy.get_operators().size(); i++) {
        operatorsAtTnow.push_back(capsule.new_variable());
    }
    operatorVars.push_back(operatorsAtTnow);
}

void sat_step_binary(TaskProxy task_proxy, sat_capsule & capsule) {
    binaryFactsAtTnow.swap(binaryFactsAtTplusOne);
    // Replace all the variables in binaryFactsAtTplusOne with new variables for the current time step.
    for (size_t i=0; i<binaryFactsAtTplusOne.size(); i++) {
        vector<int> newVariables;
        if (newVariables.size()<=0) {
            for (size_t j=0; j<binaryFactsAtTplusOne[i][0].size(); j++) {
                newVariables.push_back(capsule.new_variable());
            }
        }
        for (size_t j=0; j<binaryFactsAtTplusOne[i].size(); j++) {;
            for (size_t k=0; k<binaryFactsAtTplusOne[i][j].size(); k++) {
                if (binaryFactsAtTplusOne[i][j][k] < 0) {
                    binaryFactsAtTplusOne[i][j][k] = -newVariables[k];
                } else {
                    binaryFactsAtTplusOne[i][j][k] = newVariables[k];
                }
                
            }
        }
    }
    //cout << "Variables for next timestep: " << binaryFactsAtTplusOne << endl;

    // Find and add forbidden states of the binary fact mutex groups.
    forbidden_binary_states(binaryFactsAtTplusOne);

    // Create a new vector<int> with variables representing which operator was executed
    // (if true in the returned plan) at the current time step.
    vector<int> operatorsAtTnow;
    for (size_t i=0; i<task_proxy.get_operators().size(); i++) {
        operatorsAtTnow.push_back(capsule.new_variable());
    }
    operatorVars.push_back(operatorsAtTnow);
    //cout << "Operator vars for next timestep: " << operatorVars << endl;
}

void output_plan_validate(TaskProxy task_proxy, sat_capsule & capsule, bool binary) {
    cout << "Please enter the program call for an installed validator [default=validate]: ";
    string validator = "validate";
    string input_validator;
    getline(cin, validator);
    if (!input_validator.empty()) {
        validator = input_validator;
    }
    string domain_file = "domain.pddl";
    cout << "Please enter a problem file name: ";
    string problem_file;
    getline(cin, problem_file);
    /*
    char buff[FILENAME_MAX]; //create string buffer to hold path
    getcwd(buff, FILENAME_MAX);
    string current_working_dir(buff);
    */
    string plan_file = "found_plan";
    if (binary) {
        plan_file = "found_plan_binary";
    }

    int lit = capsule.number_of_variables;
    if (ipasir_solve(solver) == 10){
        int step_counter = 0;
        ofstream output;
        output.open(plan_file);
        if (!output) {
            cerr << "Error: File could not be opened" << endl;
            exit(1);
        }
        for (int v = 1; v <= lit; v++) {
            for (auto & it : operatorVars) {
                for (auto i=0; i<it.size(); i++) {
                    if (it[i] == v and ipasir_val(solver,v) > 0) {
                        output << "(" <<task_proxy.get_operators()[i].get_name() << ")" << endl;
                        step_counter++;
                    }
                }
            }
        }
        output << "; cost = " << step_counter << " (unit cost)";
        output.close();
        string full_call = validator + " " + domain_file + " " + problem_file + " " + plan_file;
        const char * cmd_call = full_call.c_str();
        int call = system(cmd_call);
        if (call == -1) {
            cerr << "Error: Failed to call the validator!" << endl;
        }
    }
}

void sat_encoding(TaskProxy task_proxy, int steps) {
    sat_capsule capsule;
    sat_init(task_proxy, capsule);

    // Add the variables reflecting the initial state of the problem.
    for (size_t i=0; i<factsAtTnow.size(); i++) {
        for (int j=0; j<factsAtTnow[i].size(); j++) {
            if (task_proxy.get_initial_state().get_values()[i] == j) {
                assertYes(solver, factsAtTnow[i][j]);
            } else {
                assertNot(solver, factsAtTnow[i][j]);
            }
        }
    }

    for (int timeStep=0; timeStep<steps; timeStep++) {
        // Add clauses reflecting the mutex condition of a group of variables.
        for (size_t i=0; i<factsAtTplusOne.size(); i++) {
            atLeastOne(solver, capsule, factsAtTplusOne[i]);
            atMostOne(solver, capsule, factsAtTplusOne[i]);
        }

        // Vector to collect actions/operators executing the same effects.
        vector<vector<vector<int>>> frameAxioms;
        for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
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
        for (auto i=0; i<frameAxioms.size(); i++) {
            for (auto j=0; j<frameAxioms[i].size(); j++) {
                int neg = factsAtTnow[i][j];
                int pos = factsAtTplusOne[i][j];
                impliesPosAndNegImpliesOr(solver, pos, neg, frameAxioms[i][j]);
            }
        }

        // Add clauses such that exactly one operator can be picked per time step.
        atLeastOne(solver, capsule, operatorVars[timeStep]);
        atMostOne(solver, capsule, operatorVars[timeStep]);

        // At the end of one step prepare the next time step, if it isn't the last.
        if (timeStep == steps-1) {
            break;
        } else {
            sat_step(task_proxy, capsule);
        }
    }

    // Add the variables reflecting the goal state of the problem after the last time step.
    for (size_t i=0; i<task_proxy.get_goals().size(); i++) {
        assertYes(solver, factsAtTplusOne[task_proxy.get_goals()[i].get_pair().var][task_proxy.get_goals()[i].get_pair().value]);
    }

    cout << "That many clauses have been added: " << get_number_of_clauses() << endl;
    cout << ipasir_solve(solver) << endl;
    // output_plan_validate(task_proxy, capsule, false);
    
    int lit = capsule.number_of_variables;
    if (ipasir_solve(solver) == 10){
        int step_counter = 0;
        ofstream output;
        output.open("found_plan");
        if (!output) {
            cerr << "Error: File could not be opened" << endl;
            exit(1);
        }
        for (int v = 1; v <= lit; v++) {
            for (auto & it : operatorVars) {
                for (auto i=0; i<it.size(); i++) {
                    if (it[i] == v and ipasir_val(solver,v) > 0) {
                        output << "(" <<task_proxy.get_operators()[i].get_name() << ")" << endl;
                        step_counter++;
                    }
                }
            }
        }

        output << "; cost = " << step_counter << " (unit cost)";
        output.close();
        string validator = "validate";
        string domain_file = "domain.pddl";
        string problem_file = "problem-p01.pddl";
        string plan_file = "found_plan";
        string full_call = validator + " " + domain_file + " " + problem_file + " " + plan_file;
        const char * cmd_call = full_call.c_str();
        system(cmd_call);
    }
}

void sat_encoding_binary(TaskProxy task_proxy, int steps) {
    sat_capsule capsule;
    sat_init_binary(task_proxy, capsule);

    // Add the binary variables reflecting the initial state of the problem.
    for (size_t i=0; i<binaryFactsAtTnow.size(); i++) {
        for (size_t j=0; j<binaryFactsAtTnow[i].size(); j++) {
            if (task_proxy.get_initial_state().get_values()[i] == j) {
                for (size_t k=0; k<binaryFactsAtTnow[i][j].size(); k++) {
                    // Since polarity of the variables is already embedded in their encoding
                    // they can be inserted as they are.
                    assertYes(solver, binaryFactsAtTnow[i][j][k]);
                }
            }
        }
    }

    for (int timeStep=0; timeStep<steps; timeStep++) {
        // Add clauses reflecting the operators at the current time step.
        for (OperatorProxy const & operators : task_proxy.get_operators()) {
            int operatorVar = operatorVars[timeStep][operators.get_id()];
            for (FactProxy const & preconditions : operators.get_preconditions()) {
                for (size_t i=0; i<binaryFactsAtTnow[preconditions.get_pair().var][preconditions.get_pair().value].size(); i++) {
                    implies(solver, operatorVar, binaryFactsAtTnow[preconditions.get_pair().var][preconditions.get_pair().value][i]);
                }
            }
            for (EffectProxy const & effects : operators.get_effects()) {
                for (size_t i=0; i<binaryFactsAtTplusOne[effects.get_fact().get_pair().var][effects.get_fact().get_pair().value].size(); i++) {
                    implies(solver, operatorVar, binaryFactsAtTplusOne[effects.get_fact().get_pair().var][effects.get_fact().get_pair().value][i]);
                }
            }
        }

        // Vector to collect frame axiom operators.
        vector<vector<vector<int>>> frameAxioms;
        for (auto i=0; i<binaryFactsAtTnow.size(); i++) {
            vector<vector<int>> variable;
            for (auto j=0; j<=0; j++) {
                for (auto k=0; k<binaryFactsAtTnow[i][j].size(); k++) {
                    vector<int> upwardFlank;
                    variable.push_back(upwardFlank);
                    vector<int> downwardFlank;
                    variable.push_back(downwardFlank);
                }
            }
        	frameAxioms.push_back(variable);
        }

        // Find all frame axioms.
        for (OperatorProxy const & operators : task_proxy.get_operators()) {
            int operatorVar = operatorVars[timeStep][operators.get_id()];
            for (EffectProxy const & effects : operators.get_effects()) {
                int effVar = effects.get_fact().get_pair().var;
                // TODO: Not sure, if this is the best way to do this?!
                bool matchFound = false;
                for (FactProxy const & preconditions : operators.get_preconditions()) {
                    if (preconditions.get_pair().var == effVar) {
                        matchFound = true;
                        for (auto i=0; i<binaryFactsAtTnow[effVar][preconditions.get_pair().value].size(); i++) {
                            // Add operator to upward flank vector of fact variable i.
                            if (binaryFactsAtTnow[effVar][preconditions.get_pair().value][i]<0 && 
                                binaryFactsAtTplusOne[effVar][effects.get_fact().get_pair().value][i]>0) {
                                    frameAxioms[effVar][0+2*i].push_back(operatorVar);
                            // Add operator to downward flank vector of fact variable i.
                            } else if (binaryFactsAtTnow[effVar][preconditions.get_pair().value][i]>0 && 
                                binaryFactsAtTplusOne[effVar][effects.get_fact().get_pair().value][i]<0) {
                                    frameAxioms[effVar][1+2*i].push_back(operatorVar);
                            // var stays positive
                            }
                        }
                    }
                }
                if (!matchFound && binaryFactsAtTplusOne[effVar].size() == 2) {
                    // Add operator to downward flank vector of fact variable. Special case when the
                    // effect doen't have a corresponding precondition in the operator.
                    frameAxioms[effVar][1].push_back(operatorVar);
                }
            }
        }
        for (auto i=0; i<frameAxioms.size(); i++) {
            for (auto j=0; j<frameAxioms[i].size(); j++) {
                if (j%2 == 0 && frameAxioms[i][j].size()>0) {
                    // upward flank
                    int neg = -binaryFactsAtTnow[i][0][j/2];
                    int pos = -binaryFactsAtTplusOne[i][0][j/2];
                    impliesPosAndNegImpliesOr(solver, pos, neg, frameAxioms[i][j]);
                } else if (j%2 == 1 && frameAxioms[i][j].size()>0) {
                    // downward flank
                    int pos = -binaryFactsAtTnow[i][0][j/2];
                    int neg = -binaryFactsAtTplusOne[i][0][j/2];
                    impliesPosAndNegImpliesOr(solver, pos, neg, frameAxioms[i][j]);
                }
            }
        }

        // Add clauses such that exactly one operator can be picked per time step.
        atLeastOne(solver, capsule, operatorVars[timeStep]);
        atMostOne(solver, capsule, operatorVars[timeStep]);

        // At the end of one step prepare the next time step, if it isn't the last.
        if (timeStep == steps-1) {
            break;
        } else {
            sat_step_binary(task_proxy, capsule);
        }
    }
    // Add the variables reflecting the goal state of the problem after the last time step.
    for (size_t i=0; i<task_proxy.get_goals().size(); i++) {
        for (size_t j=0; j<binaryFactsAtTplusOne[task_proxy.get_goals()[i].get_pair().var][task_proxy.get_goals()[i].get_pair().value].size(); j++) {
            assertYes(solver, binaryFactsAtTplusOne[task_proxy.get_goals()[i].get_pair().var][task_proxy.get_goals()[i].get_pair().value][j]);
        }
    }
    // TODO: Make this part a helper function!
    cout << "That many clauses have been added: " << get_number_of_clauses() << endl;
    cout << ipasir_solve(solver) << endl;
    // output_plan_validate(task_proxy, capsule, true);
    
    int lit = capsule.number_of_variables;
    if (ipasir_solve(solver) == 10){
        int step_counter = 0;
        ofstream output;
        output.open("found_plan_binary");
        if (!output) {
            cerr << "Error: File could not be opened" << endl;
            exit(1);
        }
        for (int v = 1; v <= lit; v++) {
            for (auto & it : operatorVars) {
                for (auto i=0; i<it.size(); i++) {
                    if (it[i] == v and ipasir_val(solver,v) > 0) {
                        output << "(" <<task_proxy.get_operators()[i].get_name() << ")" << endl;
                        step_counter++;
                    }
                }
            }
        }
        output << "; cost = " << step_counter << " (unit cost)";
        output.close();
        string validator = "validate";
        string domain_file = "domain.pddl";
        string problem_file = "problem-p01.pddl";
        string plan_file = "found_plan_binary";
        string full_call = validator + " " + domain_file + " " + problem_file + " " + plan_file;
        const char * cmd_call = full_call.c_str();
        system(cmd_call);
    }
}

}
