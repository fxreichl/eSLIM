#ifndef RELATIONSYNTHESISER_H__
#define RELATIONSYNTHESISER_H__

#include <vector>
#include <unordered_map>

#include "cadical.h"

namespace circuit_synthesis {

using booleanRelation = std::vector<std::pair<std::vector<int>, std::vector<int>>>;

struct Config {
  int gate_size;
  bool aig;
  bool constant_outputs;
  bool inputs_as_outputs;
  bool trivial_rule;
  bool all_steps_rule;
  bool no_reapplication_rule;
  bool ordered_steps_rule;
  Config( int gate_size, bool aig, bool constant_outputs, bool inputs_as_outputs, 
          bool trivial_rule, bool all_steps_rule, bool no_reapplication_rule, bool ordered_steps_rule) 
          : gate_size(gate_size), aig(aig), constant_outputs(constant_outputs), inputs_as_outputs(inputs_as_outputs),
            trivial_rule(trivial_rule), all_steps_rule(all_steps_rule), no_reapplication_rule(no_reapplication_rule), 
            ordered_steps_rule(ordered_steps_rule) {}
};

class RelationSynthesiser {
 public:
  RelationSynthesiser(const booleanRelation& relation, const std::vector<std::pair<int,int>>& potential_cycles, 
                      const std::vector<int>& inputs, const std::vector<int>& outputs, int max_size, const Config& cfg);
  // 10 realisable, 20 not realisable, -1 unknown (e.g. timeout)
  // timeout == 0 -> do not use a timeout
  int checkSize(unsigned int size, double timeout);
  int checkSize(unsigned int size);
  std::vector<int> getModel();

  const std::vector<std::vector<int>>& getSelectionVariables() const;
  const std::vector<std::vector<int>>& getDefinitionVariables() const;
  const std::vector<std::vector<int>>& getOutputVariables() const;

  void toggleNoReapplicationRule();

 private:
  CadicalSolver solver;
  const Config& config;
  const booleanRelation& relation;
  const std::vector<std::pair<int,int>>& potential_cycles;
  const std::vector<int>& inputs;
  const std::vector<int>& outputs;
  unsigned int max_size; // The maximal circuit size that can be checked
  int max_var;  // The maximal variable occurring in inputs/outputs
  int symmetry_selector;
  int symmetry_selector_assignment;

  std::vector<int> gate_activation_variables;
  std::vector<std::vector<int>> selection_variables;
  std::vector<std::vector<int>> gate_definition_variables;
  std::vector<std::vector<int>> gate_output_variables;
  std::vector<std::vector<int>> gate_variables;
  std::unordered_map<int, std::vector<int>> connection_variables;

  std::unordered_map<int,int> input_index_map;
  std::unordered_map<int,int> output_index_map;


  int getNewVariable();
  std::vector<int> getNewVariableVector(unsigned int size);
  void setupEncoding();
  void setupVariables();
  void setupStructuralConstraints();
  void setupSymmetryBreaking();
  void setupEquivalenceConstraints();

  void constrainSelectionVariables();
  void constraintGateOutputVariables();
  void setupCompatibilityConstraints();
  void setupCycleConstraints();
  void setupAigerConstraints();

  int setupOutputVariable(int output_index, int tt_index, const std::vector<int>& input_assm);
  void setupConnectionVariables();
  // If we have multiple cyclic pairs, different pairs may form form a cycle together
  // Assume we have two different pairs (x,y) and (a,b) in potential_cycles.
  // It can be the case that x is connected to b and a is connected to y. 
  // To rule out cycles of this kind we make use of the following idea:
  // If (x,y) is in self.potential_cycles then there is a path from x to y that is not part of the current subcircuit.
  // Now if b is connected to x, this means that y is also connected to b.
  // Thus, all gates that use y as an input are connected to b.
  void connectionVariablesForCombinedCycles();
  void addCycleConstraints();

  void addNonTrivialConstraint();
  void addUseAllStepsConstraint();
  void addNoReapplicationConstraint();
  void addOrderedStepsConstraint();

  std::vector<std::vector<int>> getCompatibilityPrefixes(const std::vector<int>& indices, int first_gate) const;
  void setCompatibilityInputValues( std::vector<int>& gate_values, const std::vector<int>& indices, 
                                    int first_gate_input, int tt_line) const;
  void updateCompatibilityInputValues(std::vector<int>& gate_values, int tt_line, int gate_line) const;

  // activator = -1: do not use an activation variable
  void addCardinalityConstraint(const std::vector<int>& vars, unsigned int cardinality, int activator = 0);
  void addSequentialCounter(const std::vector<int>& vars, unsigned int cardinality, int activator = 0);

  void defineConjunction(int var, std::vector<int>&& literals, int activator);
  void defineDisjunction(int var, std::vector<int>&& literals, int activator);

  // computes the index of the first gate that can used the indexed nodes as inputs
  // indices must be ordered
  int getPotentialSuccessors(const std::vector<int>& indices) const;
  // computes the first position where the corresponding index describes a gate. 
  int getFirstGateInput(const std::vector<int>& indices) const;
  int getIndexOffset(int tt_index, const std::vector<int>& indices) const;

  // 1 if true, -1 if false
  static int getPolarity(int idx, int shift);
  static int pow2(int x);
  static int getTruthTableLine(const std::vector<int>& inputs, const std::unordered_map<int,int>& index_map);

};

inline int RelationSynthesiser::getNewVariable() {
  return ++max_var;
}

inline std::vector<int> RelationSynthesiser::getNewVariableVector(unsigned int size) {
  std::vector<int> vars;
  vars.reserve(size);
  for (int i = 0; i < size; i++) {
    vars.push_back(getNewVariable());
  }
  return vars;
}

inline int RelationSynthesiser::getPotentialSuccessors(const std::vector<int>& indices) const {
  if (indices.back() < inputs.size()) {
    return 0;
  }
  return indices.back() - inputs.size() + 1;
}

inline int RelationSynthesiser::getFirstGateInput(const std::vector<int>& indices) const {
  for (int i = 0; i < indices.size(); i++) {
    if (indices[i] >= inputs.size()) {
      return i;
    } 
  }
  return indices.size();
}

// A subcircuit may either depend on a PI or on another gate.
inline int RelationSynthesiser::getIndexOffset(int tt_index, const std::vector<int>& indices) const {
  int offset = 0;
  for (int i = 0; i < indices.size(); i++) {
    if (indices[i] >= inputs.size()) {
      return offset;
    }
    offset += pow2(config.gate_size - i - 1) * (((tt_index + 1) >> (inputs.size() - indices[i] - 1)) & 1);
  }
  return offset;
}

inline void RelationSynthesiser::toggleNoReapplicationRule() {
  symmetry_selector_assignment = -symmetry_selector_assignment;
}


inline const std::vector<std::vector<int>>& RelationSynthesiser::getSelectionVariables() const {
  return selection_variables;
}
  
inline const std::vector<std::vector<int>>& RelationSynthesiser::getDefinitionVariables() const {
  return gate_definition_variables;
}

inline const std::vector<std::vector<int>>& RelationSynthesiser::getOutputVariables() const {
  return gate_output_variables;
}


inline int RelationSynthesiser::getPolarity(int idx, int shift) {
  return 1 - 2 * ((idx >> shift) & 1);
}

inline int RelationSynthesiser::pow2(int x) {
  return 1 << x;
}

// We subtract one as we do not keep the first line of the truth table.
// The first line represents the case where all inputs are False.
// As we have normal gates all gates ans also all outputs must be false.
// As the subcircuits are normal circuits there outputs are false if all of their inputs are false.
// We use the map such that we do not need to rely on the order of inputs.
inline int RelationSynthesiser::getTruthTableLine(const std::vector<int>& inputs, const std::unordered_map<int,int>& index_map) {
  int index = 0;
  for (int i : inputs) {
    index += (i > 0) * pow2(inputs.size() - index_map.at(abs(i)) - 1);
  }
  return index - 1;
}

}


#endif