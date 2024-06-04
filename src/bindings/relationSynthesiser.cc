#include <algorithm>
#include <unordered_set>
#include <cassert>

#include "relationSynthesiser.h"


namespace circuit_synthesis {


RelationSynthesiser::RelationSynthesiser( const booleanRelation& relation, const std::vector<std::pair<int,int>>& potential_cycles, 
                                          const std::vector<int>& inputs, const std::vector<int>& outputs, int max_size, 
                                          const Config& cfg) 
                                        : relation(relation), potential_cycles(potential_cycles), inputs(inputs), 
                                          outputs(outputs), max_size(max_size), config(cfg) {
  max_var = std::max(*std::max_element(inputs.begin(), inputs.end()), *std::max_element(outputs.begin(), outputs.end()));
  symmetry_selector = getNewVariable();
  symmetry_selector_assignment = symmetry_selector;
  gate_activation_variables.reserve(max_size);
  for (int i = 0; i < max_size; i++) {
    gate_activation_variables.push_back(getNewVariable());
  }

  for (int i = 0; i < inputs.size(); i++) {
    input_index_map[inputs[i]] = i;
  }
  for (int i = 0; i < outputs.size(); i++) {
    output_index_map[outputs[i]] = i;
  }
  setupEncoding();
}

int RelationSynthesiser::checkSize(unsigned int size) {
  return checkSize(size, 0);
}

int RelationSynthesiser::checkSize(unsigned int size, double timeout) {
  std::vector<int> assumptions;
  assumptions.reserve(max_size + 1);
  for (int i = 0; i < size; i++) {
    assumptions.push_back(gate_activation_variables[i]);
  }
  for (int i = size; i < max_size; i++) {
    assumptions.push_back(-gate_activation_variables[i]);
  }
  assumptions.push_back(symmetry_selector_assignment);
  if (timeout == 0) {
    return solver.solve(assumptions);
  } else {
    return solver.solve(timeout, assumptions);
  }
}

// checkSize must have been called before
// checkSize must have yielded 10
std::vector<int> RelationSynthesiser::getModel() {
  return solver.getModel();
}

void RelationSynthesiser::setupEncoding() {
  setupVariables();
  setupStructuralConstraints();
  setupSymmetryBreaking();
  setupEquivalenceConstraints();
}

void RelationSynthesiser::setupVariables() {
  gate_activation_variables.reserve(max_size);
  selection_variables.reserve(max_size);
  gate_definition_variables.reserve(max_size);
  gate_variables.reserve(max_size);
  for (int i = 0; i < max_size; i++) {
    gate_activation_variables.push_back(getNewVariable());
    selection_variables.push_back(getNewVariableVector(inputs.size() + i));
    gate_definition_variables.push_back(getNewVariableVector(pow2(config.gate_size) - 1));
    gate_variables.push_back(getNewVariableVector(pow2(inputs.size()) - 1));
  }
  gate_output_variables.reserve(max_size + config.constant_outputs + config.inputs_as_outputs * inputs.size());
  for (int i = 0; i < max_size + config.constant_outputs + config.inputs_as_outputs * inputs.size(); i++) {
    gate_output_variables.push_back(getNewVariableVector(outputs.size()));
  }
  if (!potential_cycles.empty()) {
    for (const auto& [out, in] : potential_cycles) {
      if (connection_variables.find(in) == connection_variables.end()) {
        connection_variables[in] = getNewVariableVector(max_size + inputs.size());
      }
    }
  }
}

void RelationSynthesiser::setupStructuralConstraints() {
  constrainSelectionVariables();
  constraintGateOutputVariables();
  setupCompatibilityConstraints();
  if (!potential_cycles.empty()) {
    setupCycleConstraints();
  }
  if (config.aig) {
    setupAigerConstraints();
  }
}

void RelationSynthesiser::setupSymmetryBreaking() {
  if (config.trivial_rule) {
    addNonTrivialConstraint();
  }
  if (config.all_steps_rule) {
    addUseAllStepsConstraint();
  }
  if (config.no_reapplication_rule) {
    addNoReapplicationConstraint();
  }
  if (config.ordered_steps_rule) {
    addOrderedStepsConstraint();
  }
  
}

void RelationSynthesiser::constrainSelectionVariables() {
  for (int i = 0; i < max_size; i++) {
    addCardinalityConstraint(selection_variables[i], config.gate_size, -gate_activation_variables[i]);
  }
}

void RelationSynthesiser::constraintGateOutputVariables() {
  // If the activation variable is false then the gate must not be an output
  for (int i = 0; i < max_size; i++) {
    for (int v : gate_output_variables[i]) {
      solver.addClause({gate_activation_variables[i], -v});
    }
  }
  for (int i = 0; i < outputs.size(); i++) {
    std::vector<int> clause;
    clause.reserve(max_size + config.constant_outputs + config.inputs_as_outputs * inputs.size());
    for (int j = 0; j < max_size + config.constant_outputs + config.inputs_as_outputs * inputs.size(); j++) {
      clause.push_back(gate_output_variables[j][i]);
    }
    addCardinalityConstraint(clause, 1);
  }
}


void RelationSynthesiser::setupCompatibilityConstraints() {
  std::vector<bool> filter(config.gate_size, 1);
  // A 1 at index i indicates that the ith node is used as an input.
  // By using prev_permutation we get all possible permutations of the filter
  filter.resize(inputs.size() + max_size - 1);
  std::vector<int> indices(config.gate_size,0);
  int tt_size = RelationSynthesiser::pow2(inputs.size()) - 1;
  do {
    indices.clear();
    for (int i = 0; i < inputs.size() + max_size - 1; i++) {
			if (filter[i]) {
				indices.push_back(i);
			}
		}
    // All gates starting from this index can depend on the current selection
    int first_gate = getPotentialSuccessors(indices);
    // The first non-PI input
    int first_gate_input = getFirstGateInput(indices);
    int nof_non_pi_inputs = config.gate_size - first_gate_input;
    std::vector<std::vector<int>> prefixes = getCompatibilityPrefixes(indices, first_gate);
    std::vector<int> input_values(config.gate_size - first_gate_input, 0);
    for (int tt = 0; tt < tt_size; tt++) {
      int offset = getIndexOffset(tt, indices);
      setCompatibilityInputValues(input_values, indices, first_gate_input, tt);
      int start_with = 0;
      if (offset == 0) {
        start_with = 1;
        for (int j = 0; j < prefixes.size(); j++) {
          solver.addCombinedClause(prefixes[j], input_values, {-gate_variables[first_gate + j][tt]});
        }
      }
      for (int i = start_with; i < pow2(nof_non_pi_inputs); i++) {
        updateCompatibilityInputValues(input_values, tt, i);
        for (int j = 0; j < prefixes.size(); j++) {
          std::vector<int> cl {-gate_definition_variables[first_gate + j][offset + i - 1], gate_variables[first_gate + j][tt]};
          solver.addCombinedClause(prefixes[j], input_values, cl);
          cl[0] = -cl[0];
          cl[1] = -cl[1];
          solver.addCombinedClause(prefixes[j], input_values, cl);
        }
      }
    }
  // we want to start with 1..10..0 thus we use prev_permutation instead of next_permutation
  } while (std::prev_permutation(filter.begin(), filter.end()));
}

void RelationSynthesiser::setupEquivalenceConstraints() {
  if (relation.empty()) {
    return;
  }
  std::unordered_map<int, std::unordered_map<int,int>> output_variable_map;
  for (const auto& [in, out] : relation) {
    int tt_index = getTruthTableLine(in, input_index_map);
    // If all inputs are negative then also all the outputs are negative as we have normal chains.
    // Thus, we do not need any constraint for this case.
    if (tt_index == -1) {
      continue;
    }
    std::vector<int> clause;
    clause.reserve(out.size());
    for (int o : out) {
      if (output_variable_map.find(abs(o)) == output_variable_map.end()) {
        output_variable_map[abs(o)] = std::unordered_map<int,int>();
      }
      int out_var;
      if (output_variable_map.at(abs(o)).find(tt_index) == output_variable_map.at(abs(o)).end()) {
        out_var = setupOutputVariable(output_index_map.at(abs(o)), tt_index, in);
        output_variable_map[abs(o)][tt_index] = out_var;
      } else {
        out_var = output_variable_map[abs(o)][tt_index];
      }
      if (o < 0) {
        clause.push_back(out_var);
      } else {
        clause.push_back(-out_var);
      }
    }
    solver.addClause(clause);
  }
}

int RelationSynthesiser::setupOutputVariable(int output_index, int tt_index, const std::vector<int>& input_assm) {
  int var = getNewVariable();
  std::vector<int> clause;
  for (int i = 0; i < max_size; i++) {
    clause.assign({-gate_activation_variables[i], -gate_output_variables[i][output_index], -gate_variables[i][tt_index], var});
    solver.addClause(clause);
    clause[2] = -clause[2];
    clause[3] = -clause[3];
    solver.addClause(clause);
  }
  if (config.inputs_as_outputs) {
    for (int i : input_assm) {
      if (i > 0) {
        clause.assign({-gate_output_variables[input_index_map.at(i) + max_size][output_index], var});
      } else {
        clause.assign({-gate_output_variables[input_index_map.at(-i) + max_size][output_index], -var});
      }
      solver.addClause(clause);
    }
  }
  if (config.constant_outputs) {
    clause.assign({-gate_output_variables.back()[output_index], -var});
    solver.addClause(clause);
  }
  return var;
}

void RelationSynthesiser::setupCycleConstraints() {
  assert (!potential_cycles.empty());
  setupConnectionVariables();
  if (potential_cycles.size() > 1) {
    connectionVariablesForCombinedCycles();
  }
  addCycleConstraints();
}

void RelationSynthesiser::addCycleConstraints() {
  for (const auto& [outp, inp] : potential_cycles) {
    int output_idx = output_index_map.at(outp);
    for (int i = 0; i < max_size; i++) {
      solver.addClause({-gate_activation_variables[i], -gate_output_variables[i][output_idx], -connection_variables.at(inp)[i + inputs.size()]});
    }
    if (config.inputs_as_outputs) {
      for (int i = 0; i < inputs.size(); i++) {
        solver.addClause({-gate_output_variables[max_size + i][output_idx], -connection_variables.at(inp)[i]});
      }
    }
  }
}

void RelationSynthesiser::setupConnectionVariables() {
  for (const auto& [input_var, connection_vars] : connection_variables) {
    int input_idx = input_index_map.at(input_var);
    // An input is connected to itself
    solver.addClause({connection_vars[input_idx]});
    for (int i = 0; i < max_size; i++) {
      int activation_variable = gate_activation_variables[i];
      for (int j = 0; j < inputs.size(); j++) {
        // if gate i uses input j and input j is connected to input_var then also gate i is connected to input_var
        solver.addClause({-activation_variable, -selection_variables[i][j], -connection_vars[j], connection_vars[inputs.size() + i]});
      }
      for (int j = 0; j < i; j++) {
        // if gate i uses gate j and gate j is connected to input_var then also gate i is connected to input_var 
        solver.addClause({-activation_variable, -selection_variables[i][inputs.size() + j], -connection_vars[inputs.size() + j], connection_vars[inputs.size() + i]});
      }
    }
  }
}


void RelationSynthesiser::connectionVariablesForCombinedCycles() {
  assert (potential_cycles.size() > 1);
  // Inputs are assigned to the outputs on which they depend
  std::unordered_map<int, std::unordered_set<int>> inputs_per_output;
  // Inputs in pairs
  std::unordered_set<int> inputs_in_pairs;
  for (const auto& [out, in] : potential_cycles) {
    if (inputs_per_output.find(out) == inputs_per_output.end()) {
      inputs_per_output[out] = {in};
    } else {
      inputs_per_output[out].insert(in);
    }
    inputs_in_pairs.insert(in);
  }
  for (const auto& [ov, inp] : inputs_per_output) {
    for (int iv : inputs_in_pairs) {
      if (inp.find(iv) == inp.end()) {
        for (int k : inputs_per_output.at(ov)) {
          for (int i = 0; i < max_size; i++) {
            // Input k depends on output ov. 
            // If gate i represents output ov and gate i is connected to iv then also gate k is connected to iv.
            solver.addClause({-gate_activation_variables[i], -gate_output_variables[i][output_index_map.at(ov)], 
                            -connection_variables.at(iv)[inputs.size() + i], connection_variables.at(iv)[input_index_map.at(k)]});
          }
          if (config.inputs_as_outputs) {
            for (int i = 0; i < inputs.size(); i++) {
              // Input k depends on output ov. 
              // If input i represents output ov and input i is connected to iv then gate k shall be connected to iv too.
              solver.addClause({-gate_output_variables[max_size + i][output_index_map.at(ov)], -connection_variables.at(iv)[i], connection_variables.at(iv)[input_index_map.at(k)]});
            }
          }
        }
      }
    }
  }
}

void RelationSynthesiser::setupAigerConstraints() {
  assert (config.gate_size == 2);
  for (int i = 0; i < max_size; i++) {
    solver.addClause({-gate_definition_variables[i][0], -gate_definition_variables[i][1], gate_definition_variables[i][2]});
  }
}

std::vector<std::vector<int>> RelationSynthesiser::getCompatibilityPrefixes(const std::vector<int>& indices, int first_gate) const {
  std::vector<std::vector<int>> clauses;
  clauses.reserve(max_size - first_gate);
  for (int i = first_gate; i < max_size; i++) {
    std::vector<int> clause;
    clause.reserve(config.gate_size + 1);
    clause.push_back(-gate_activation_variables[i]);
    for (int j = 0; j < config.gate_size; j++) {
      clause.push_back(-selection_variables[i][indices[j]]);
    }
    clauses.push_back(clause);
  }
  return clauses;
}

void RelationSynthesiser::setCompatibilityInputValues(std::vector<int>& gate_values, const std::vector<int>& indices, 
                                                      int first_gate_input, int tt_line) const {
  for (int i = first_gate_input; i < config.gate_size; i++) {
    int input_index = indices[i] - inputs.size();
    gate_values[i - first_gate_input] = gate_variables[input_index][tt_line];
  }
}

void RelationSynthesiser::updateCompatibilityInputValues(std::vector<int>& gate_values, int tt_line, int gate_line) const {
  for (int i = 0; i < gate_values.size(); i++) {
    int polarity = getPolarity(gate_line, gate_values.size() - i - 1);
    gate_values[i] = polarity * abs(gate_values[i]);
  }
}


void RelationSynthesiser::addCardinalityConstraint(const std::vector<int>& vars, unsigned int cardinality, int activator) {
  assert (cardinality > 0);
  assert (vars.size() >= cardinality);
  if (vars.size() == cardinality) {
    std::vector<int> clause;
    if (activator != 0) {
      clause.push_back(activator);
    }
    for (int var : vars) {
      clause.push_back(var);
      solver.addClause(clause);
      clause.pop_back();
    }
  } else {
    addSequentialCounter(vars, cardinality, activator);
  }
}

// see Carsten Sinz: Towards an Optimal CNF Encoding of Boolean Cardinality Constraints
// As we want that exactly cardinality many variables are set to true we need additional constraints.
// Because of this reason we cannot use the single polarity encoding presented in the paper
void RelationSynthesiser::addSequentialCounter(const std::vector<int>& vars, unsigned int cardinality, int activator) {
  assert (vars.size() > cardinality);
  std::vector<int> subcircuit_outputs {vars.front()}, last_subcircuit_outputs;
  for (int i = 1; i < vars.size() - 1; i++) {
    int v = vars[i];
    int in_var = v;
    std::swap(subcircuit_outputs, last_subcircuit_outputs);
    subcircuit_outputs.clear();
    for (int j = 0; j < last_subcircuit_outputs.size(); j++) {
      int orv  = getNewVariable();
      defineDisjunction(orv, {in_var, last_subcircuit_outputs[j]}, activator);
      subcircuit_outputs.push_back(orv);
      if (j == cardinality - 1) {
        // if both would be true then at least cardinality + 1 many variables would be true
        solver.addClause({-last_subcircuit_outputs.back(), -v});
      } else {
        in_var = getNewVariable();
        defineConjunction(in_var, {v, last_subcircuit_outputs[j]}, activator);
      }
    }
    if (last_subcircuit_outputs.size() < cardinality) {
      subcircuit_outputs.push_back(in_var);
    }
  }
  solver.addClause({-subcircuit_outputs.back(), -vars.back()});

  // Either subcircuit_outputs.back() is true or subcircuit_outputs[-2] and vars.back() is true
  std::vector<int> clause {subcircuit_outputs.back(), vars.back()};
  solver.addClause(clause);
  if (cardinality > 1) {
    clause.pop_back();
    clause.push_back(subcircuit_outputs[subcircuit_outputs.size() - 2]);
    solver.addClause(clause);
  }
}


void RelationSynthesiser::defineConjunction(int var, std::vector<int>&& literals, int activator) {
  std::vector<int> big_clause, small_clause;
  if (activator != 0) {
    big_clause.reserve(literals.size() + 2);
    small_clause.reserve(3);
    big_clause.push_back(activator);
    small_clause.push_back(activator);
  } else {
    big_clause.reserve(literals.size() + 1);
    small_clause.reserve(2);
  }
  big_clause.push_back(var);
  small_clause.push_back(-var);
  for (int lit : literals) {
    big_clause.push_back(-lit);
    small_clause.push_back(lit);
    solver.addClause(small_clause);
    small_clause.pop_back();
  }
  solver.addClause(big_clause);
}

void RelationSynthesiser::defineDisjunction(int var, std::vector<int>&& literals, int activator) {
  std::vector<int> clause;
  literals.push_back(-var);
  if (activator != 0) {
    literals.push_back(activator);
    solver.addClause(literals);
    literals.pop_back();
    clause.reserve(3);
    clause.push_back(activator);
  } else {
    clause.reserve(2);
    solver.addClause(literals);
  }
  literals.pop_back();
  clause.push_back(var);
  for (int lit : literals) {
    clause.push_back(-lit);
    solver.addClause(clause);
    clause.pop_back();
  }
}

void RelationSynthesiser::addNonTrivialConstraint() {
  for (int i = 0; i < max_size; i++) {
    // We do not allow constant gates
    solver.addClause(gate_definition_variables[i]);
    // We exclude gates representing the projection to one of its inputs
    for (int j = 0; j < config.gate_size; j++) {
      int start = pow2(config.gate_size - j);
      int block_length = pow2(config.gate_size - j - 1);
      std::vector<int> clause;
      clause.reserve(pow2(config.gate_size) - 1);
      for (int k = 0; k < pow2(j); k++) {
        for (int l = k * start - (k == 0 ? 0 : 1); l < k * start + block_length -1; l++) {
          clause.push_back(gate_definition_variables[i][l]);
        }
        for (int l = k * start + block_length - 1; l < (k + 1) * start - 1; l++) {
          clause.push_back(-gate_definition_variables[i][l]);
        }
      }
      solver.addClause(clause);
    }
  }
}

// Every gate is either an output or an input of another gate
void RelationSynthesiser::addUseAllStepsConstraint() {
  for (int i = 0; i < max_size; i++) {
    std::vector<int> clause (gate_output_variables[i].begin(), gate_output_variables[i].end());
    clause.reserve(max_size - i + 1);
    for (int j = i + 1; j < max_size; j++) {
      clause.push_back(selection_variables[j][inputs.size() + i]);
    }
    clause.push_back(-gate_activation_variables[i]);
    solver.addClause(clause);
  }
}


// Suppose gate i has inputs i1,...,in and gate j uses i as an input.
// Then the other n-1 inputs of j shall not be contained in the inputs of i.
// Otherwise j could be directly represented by a gate with inputs i1,...,in
void RelationSynthesiser::addNoReapplicationConstraint() {
  std::vector<bool> filter(config.gate_size, 1);
  // A 1 at index i indicates that the ith node is used as an input.
  // By using prev_permutation we get all possible permutations of the filter
  filter.resize(inputs.size() + max_size - 1);
  std::vector<int> indices(config.gate_size,0);
  int tt_size = RelationSynthesiser::pow2(inputs.size()) - 1;
  do {
    indices.clear();
    for (int i = 0; i < inputs.size() + max_size - 1; i++) {
			if (filter[i]) {
				indices.push_back(i);
			}
		}
    int first_gate = getPotentialSuccessors(indices);
    for (int i = first_gate; i < max_size; i++) {
      std::vector<int> clause {-symmetry_selector};
      clause.reserve(inputs.size() + max_size + 1);
      for (int idx : indices) {
        clause.push_back(-selection_variables[i][idx]);
      }
      int start_with = clause.size();
      for (int j = i + 1; j < max_size; j++) {
        // gate j has inputs.size() + j potential inputs
        clause.resize(inputs.size() + j + 2, 0);
        clause[start_with] = -selection_variables[j][inputs.size() + i];
        clause[start_with + 1] = -gate_activation_variables[j];
        int k = 0, l = 0, m = 0;
        // while (k < inputs.size() + j && l < indices.size()) {
        while (k < inputs.size() + j) {
          if (l >= indices.size() || k < indices[l]) {
            if (k != inputs.size() + i) {
              clause[start_with + m + 2] = selection_variables[j][k];
              m++;
            }
            k++;
          } else if (k > indices[l]) {
            l++;
          } else {
            k++;
            l++;
          }
        }
        // for (int l = k; l < inputs.size() + j; l++) {
        //   if (l != inputs.size() + i) {
        //     clause[start_with + m + 2] = selection_variables[j][l];
        //   }
        // }
        solver.addClause(clause);
      }
    }
  } while (std::prev_permutation(filter.begin(), filter.end()));
}

// Order steps according to their inputs.
// If step i has input j then step i+1 must have an input >=j
void RelationSynthesiser::addOrderedStepsConstraint() {
  for (int i = 0; i < max_size - 1; i++) {
    for (int j = 0; j < inputs.size() + i; j++) {
      std::vector<int> clause {-gate_activation_variables[i+1], -selection_variables[i][j]};
      clause.reserve(inputs.size() + i - j + 3);
      for (int k = j; k < inputs.size() + i + 1; k++) {
        clause.push_back(selection_variables[i+1][k]);
      }
      solver.addClause(clause);
    }
  }
}


}