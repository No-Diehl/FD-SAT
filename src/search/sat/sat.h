#ifndef SAT_SAT_H
#define SAT_SAT_H

#include "../ipasir.h"
#include "../plan_manager.h"
#include "../tasks/root_task.h"
#include "../task_utils/task_properties.h"
#include "../sat_encoder.h"
#include "../utils/logging.h"

using namespace std;

namespace sat {
void sat_init(TaskProxy task_proxy,
              sat_capsule & capsule,
              vector<vector<int>> & factsAtTnow,
              vector<vector<int>> & factsAtTplusOne,
              vector<vector<int>> & operatorVars);
void forbidden_binary_states(vector<vector<vector<int>>> & binaryFacts, void * solver);
void sat_init_binary(TaskProxy task_proxy,
                     sat_capsule & capsule,
                     void * solver,
                     vector<vector<vector<int>>> & binaryFactsAtTnow,
                     vector<vector<vector<int>>> & binaryFactsAtTplusOne,
                     vector<vector<int>> & operatorVars);
void sat_step(TaskProxy task_proxy,
              sat_capsule & capsule,
              vector<vector<int>> & factsAtTnow,
              vector<vector<int>> & factsAtTplusOne,
              vector<vector<int>> & operatorVars);
void sat_step_binary(TaskProxy task_proxy,
                     sat_capsule & capsule,
                     void * solver,
                     vector<vector<vector<int>>> & binaryFactsAtTnow,
                     vector<vector<vector<int>>> & binaryFactsAtTplusOne,
                     vector<vector<int>> & operatorVars);
void found_plan(int vars,
                TaskProxy task_proxy,
                void * solver,
                const vector<vector<int>> & operatorVars,
                bool binary);
void forall_step_to_solver(sat_capsule & capsule,
                           void * solver,
                           const vector<vector<int>> & operatorVars,
                           int timeStep);
bool sat_encoding(TaskProxy task_proxy, int steps);
bool sat_encoding_binary(TaskProxy task_proxy, int steps);
void sat_forall(TaskProxy task_proxy);
void forall_chains(vector<vector<vector<int>>> & erase,
                   vector<vector<vector<int>>> & require,
                   vector<vector<vector<vector<pair<int,int>>>>> & chainVec);
void collect_invariants(TaskProxy task_proxy);
}
#endif