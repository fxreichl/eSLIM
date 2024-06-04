#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Sep  2 11:18:38 2022
@author: fs
"""
import time

import logging

from clausalEncoding import getRenamingAndClauses, getClausalEncodingSpec,\
                            getVariables, getEqualityClauses, getRenamedClause

from utils import TimeoutException
from utils import ViolatedInvariantException
                            


from bindings.CadicalPython import CadicalSolver




def getNewOutputs(spec, gate_aliases):
  return {o for g in gate_aliases for o in spec.getGateOutputs(g)
          if o not in gate_aliases}

def getFanoutCone(spec, gate_aliases):
  cone = set(gate_aliases)
  while getNewOutputs(spec, cone):
    cone.update(getNewOutputs(spec, cone))
  return cone
  

# potential_cycles contains pairs of outputs and inputs of the subcircuit
# where the input depends on the output 
def relationFromSubcircuit(spec, subcircuit_gates, potential_cycles, timeout=None):
  start = time.time()
  # logging.getLogger().setLevel(logging.INFO)
  # 1. Get clausal encoding of circuit.
  spec_encoding = getClausalEncodingSpec(spec)
  # 2. Create clausal encoding of the gates in the fanout cone, not including
  # the gates of the subcircuit itself.
  subcircuit_outputs = set(spec.getSubcircuitOutputs(subcircuit_gates))
  fanout_cone = getFanoutCone(spec, subcircuit_outputs)
  # A subcircuit output may also be the input for another gate in the subcircuit.
  # The cone shall not contain any non-output gates from the subcircuit.
  fanout_cone.difference_update(subcircuit_gates)
  fanout_cone.update(subcircuit_outputs)
  strict_fanout_cone = fanout_cone - set(subcircuit_outputs)
  fanout_encoding = getClausalEncodingSpec(spec, strict_fanout_cone)
  # 3. In the encoding from 2, rename all gates in the fanout cone.
  fanout_cone_inputs = spec.getSubcircuitInputs(fanout_cone)
  assert not fanout_cone.intersection(fanout_cone_inputs), "Input in cone."
  # If there are inputs of the subcircuit that depend on outputs of the subcircuit
  # then these inputs shall not be renamed. Otherwise, the inputs would not depend 
  # on the choice of the outputs
  if len(potential_cycles) > 0 :
    inputs_to_consider = set(x for _,x in potential_cycles)
    fanout_cone_inputs.difference_update(inputs_to_consider)
  max_variable = max(getVariables(spec_encoding))
  renamed_fanout_encoding, renaming = getRenamingAndClauses(fanout_encoding,
                                                            max_variable+1,
                                                            fanout_cone_inputs)
  outputs_to_keep = set()
  # If there are inputs that depend on outputs we have to use the renaming 
  # of these inputs in the copy of the cone.
  subcircuit_inputs  = set(spec.getSubcircuitInputs(subcircuit_gates))
  if len(potential_cycles) > 0 :
    subcircuit_input_variables = {renaming[x] if x in inputs_to_consider else x for x in subcircuit_inputs}
    # TEST: DEBUG:
    for x, y in potential_cycles :
      if x not in renaming :
        raise ViolatedInvariantException(f"Pair: {x}; {y} -- fanout cone: {strict_fanout_cone} -- renaming: {renaming}")
    #
    outputs_to_keep = set(renaming[x] for x, _ in potential_cycles)
  else :
    subcircuit_input_variables = subcircuit_inputs
  # It is possible that a subcircuit only has a single output, which is a PO.
  # In this case the strict_fanout_cone is empty.
  # Thus, also getVariables(renamed_fanout_encoding) is empty.
  if len(getVariables(renamed_fanout_encoding)) > 0 :
    max_variable = max(max_variable, max(getVariables(renamed_fanout_encoding)))
  # 4. For each output gate in the fanout cone, create a new auxiliary variable
  # encoding equality between original and renamed gate.
  pos_in_cone = [v for v in spec.getOutputs() if v in fanout_cone]
  assert len(pos_in_cone) > 0 , f"No POs in cone.\nSubcircuit: {subcircuit_gates}.\nCone: {fanout_cone}"
  logging.debug(f"POs in subcircuit's cone: {pos_in_cone}")
  # If an output of the subcircuit is a PO we also need to introduce equality clauses.
  # For this purpose we also introduce a variable for these outputs.
  # If such an output is also the input of another gate then we
  # have already introduced a renaming so we do not need to introduce a new variable.
  for x in pos_in_cone :
    if x in subcircuit_outputs and not x in renaming :
      max_variable += 1
      renaming[x] = max_variable
  inverse_renaming = {w: v for v, w in renaming.items()}
  aux_and_pos = list(enumerate(pos_in_cone, start=max_variable+1))
  equality_encoding = [c for a, v in aux_and_pos 
                       for c in getEqualityClauses(v, renaming[v], a)]
  max_variable = max(max_variable, max(getVariables(equality_encoding)))
  formula = spec_encoding + renamed_fanout_encoding + equality_encoding
  # 5. Add a clause containing all these auxiliary variables negated. Include
  # a selector so that this clause can be deactivated.
  max_variable += 1
  selector = max_variable
  one_different = [-selector] + [-aux for aux, _ in aux_and_pos]
  formula.append(one_different)
  all_equal = [aux for aux, _ in aux_and_pos]
  # 6. Repeatedly check for satisfying assignments.
  # solver = Cadical(bootstrap_with=formula)
  # solver = Glucose3(bootstrap_with=formula) #Cadical cannot be interrupted
  solver = CadicalSolver(bootstrap_with=formula)
  logging.debug(f"Inputs of subcircuit: {subcircuit_inputs}")
  logging.debug(f"Outputs of subcircuit: {subcircuit_outputs}")
  subcircuit_outputs_renamed = set(getRenamedClause(subcircuit_outputs,
                                                    renaming))
  pi_set = set(spec.getInputs())                                                  
  relation = []
  setup_time = time.time() - start
  start = time.time()
  while solver.solve_limited(timeout, [selector]) :
    if not timeout is None and time.time() - start > timeout :
      raise TimeoutException
    assignment = solver.get_model()
    logging.debug(f"Assignment: {assignment}")
    assignment_outputs_renamed = [l for l in assignment 
                                  if abs(l) in subcircuit_outputs_renamed]
    assignment_outputs = getRenamedClause(assignment_outputs_renamed,
                                          inverse_renaming)
    assignment_inputs = [l for l in assignment
                         if abs(l) in pi_set]
    assignment_subcircuit_inputs = [l for l in assignment
                                    if abs(l) in subcircuit_input_variables]
    logging.debug(f"Subcircuit inputs: {assignment_subcircuit_inputs}")
    logging.debug(f"Subcircuit outputs: {assignment_outputs}")
    assumptions = assignment_inputs + assignment_outputs_renamed + all_equal
    # assert not solve(solver, assumptions, timeout), f"Model {solver.get_model()}"
    assert not solver.solve_limited(timeout, assumptions), f"Model {solver.get_model()}"
    core_variables = {abs(l) for l in solver.get_failed(assumptions)}
    # Assume we have an input x that depends on output y.
    # Even if y is not in the core we cannot necessarily remove it from the assignment.
    # If we would remove it this would mean that no matter how we assign y 
    # the given choice of the outputs under the given assignment yields a discrepancy.
    # But the input x depends on y. So if we assign y differently we actually do not know
    # if we obtain a discrepancy.
    core_variables.update(outputs_to_keep)
    outputs_renamed_core = [l for l in assignment_outputs_renamed 
                            if abs(l) in core_variables]
    outputs_core = getRenamedClause(outputs_renamed_core,
                                    inverse_renaming)
    logging.debug(f"Core subcircuit outputs: {outputs_core}")
    logging.debug(f"Forbidding {assignment_subcircuit_inputs} with {outputs_core}")
    renamed_assignment_subcircuit_inputs = [(inverse_renaming[l] if l > 0 else -inverse_renaming[-l]) if abs(l) in inverse_renaming else l
                                            for l in assignment_subcircuit_inputs]
    relation.append((renamed_assignment_subcircuit_inputs, outputs_core))
    assignment_to_block = assignment_subcircuit_inputs + outputs_renamed_core
    blocking_clause = [-selector] + [-l for l in assignment_to_block]
    solver.add_clause(blocking_clause)
  logging.debug(f"Relation contains {len(relation)} tuples.")
  return relation, time.time() - start, setup_time