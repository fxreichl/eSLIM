# The py-aiger library seems not to be able to handle binary aiger files .
# Thus, we directly use the aiger library.

import bitarray
import bitarray.util

from specification import Specification

from bindings.build.aiger import Aiger


def getSpecification(fname) :
  aiger_interface = Aiger()
  aiger_interface.readAiger(fname)
  pis = [processAigerVariable(x) for x in aiger_interface.getInputs()]
  pos = [processAigerVariable(x) for x in aiger_interface.getOutputs()]
  pos_set = set(pos)
  spec = Specification(pis, pos)
  for idx, out in enumerate(aiger_interface.getOutputs()) :
    if isNegatedAigerLiteral(out) :
      spec.negated_pos[idx] = 1
  negated_gates = set()
  for i in range(aiger_interface.getNofAnds()) :
    addGate(spec, aiger_interface, i, negated_gates, pos_set)
  
  spec.init(False)
  return spec

def writeSpecification(fname, spec) :
  aiger_interface = Aiger()
  aiger_pis = [getAigerVariable(x) for x in spec.getInputs()]
  aiger_interface.setInputs(aiger_pis)
  constant_alias = spec.constant_gate_alias
  negated_gates = set()
  renaming = {}
  for gate in spec.orderedGateTraversal() :
    alias = gate.getAlias()
    if alias == constant_alias :
      continue
    table = gate.table.copy()
    inputs = gate.inputs 
    inputs = [renaming[x] if x in renaming else x for x in inputs]
    assert len(inputs) == 1 or len(inputs) == 2, "Non binary gate encountered"
    assert table[0] == 0, "Gates must be normal"
    if len(inputs) == 1 :
      renaming[alias] = inputs[0]
      if inputs[0] in negated_gates :
        negated_gates.add(alias)
      continue

    if inputs[0] in negated_gates :
      lhs1 = getAigerLiteral(-inputs[0])
    else :
      lhs1 = getAigerLiteral(inputs[0])
    if inputs[1] in negated_gates :
      lhs2 = getAigerLiteral(-inputs[1])
    else :
      lhs2 = getAigerLiteral(inputs[1])

    if table.count() == 3 :
      negated_gates.add(alias)
      aiger_interface.addAnd(negateAigerLiteral(lhs1), negateAigerLiteral(lhs2), getAigerVariable(alias))
    else :
      assert table.count() == 1, "Invalid aiger gate encountered"
      if table[1] == 1 :
        aiger_interface.addAnd(negateAigerLiteral(lhs1), lhs2, getAigerVariable(alias))
      elif table[2] == 1 :
        aiger_interface.addAnd(lhs1, negateAigerLiteral(lhs2), getAigerVariable(alias))
      elif table[3] == 1 :
        aiger_interface.addAnd(lhs1, lhs2, getAigerVariable(alias))
      else :
        assert False, "Normal gate cannot be the conjunction of negations"

  aiger_pos = []
  for i, out in enumerate(spec.getOutputs()) :
    if constant_alias is not None and out == constant_alias :
      if spec.isOutputNegated(i) :
        aiger_pos.append(aiger_interface.getConstantTrue())
      else :
        aiger_pos.append(aiger_interface.getConstantFalse())
    else :
      if out in renaming :
        out = renaming[out]
      if out in negated_gates :
        aiger_literal = getAigerLiteral(-out)
      else :
        aiger_literal = getAigerLiteral(out)
      if spec.isOutputNegated(i) :
        aiger_pos.append(negateAigerLiteral(aiger_literal))
      else :
        aiger_pos.append(aiger_literal)
  aiger_interface.setOutputs(aiger_pos)

  if fname.endswith(".aag") :
    write_ok = aiger_interface.writeAiger(fname, False)
  else :
    write_ok = aiger_interface.writeAiger(fname, True)
  if not write_ok :
    print("Could not write AIG.")

def addGate(spec, aiger_interface, gate_idx, negated_gates, pos_set) :
  lhs, rhs1, rhs2 = aiger_interface.getAnd(gate_idx)
  alias = processAigerVariable(lhs)
  if rhs1 == aiger_interface.getConstantFalse() or rhs2 == aiger_interface.getConstantFalse() :
    spec.addGateUnsorted(alias, [], bitarray.util.zeros(1))
  elif rhs1 == aiger_interface.getConstantTrue() :
    if rhs2 == aiger_interface.getConstantTrue() :
      spec.addGateUnsorted(alias, [], bitarray.util.zeros(1))
      negated_gates.add(alias)
      if alias in pos_set :
        # we toggle the value as the output may already be negated - in an AIG an output may be the negation of a gate
        spec.toggleOutputNegation(alias)
    else :
      if processAigerVariable(rhs2) in negated_gates :
        rhs2 = negateAigerLiteral(rhs2)
      spec.addGateUnsorted(alias, [processAigerVariable(rhs2)], bitarray.bitarray([0,1]))
      if isNegatedAigerLiteral(rhs2) :
        negated_gates.add(alias)
        if alias in pos_set :
          spec.toggleOutputNegation(alias)
  elif rhs2 == aiger_interface.getConstantTrue() :
    if processAigerVariable(rhs1) in negated_gates :
      rhs1 = negateAigerLiteral(rhs1)
    spec.addGateUnsorted(alias, [processAigerVariable(rhs1)], bitarray.bitarray([0,1]))
    if isNegatedAigerLiteral(rhs1) :
      negated_gates.add(alias)
      if alias in pos_set :
        spec.toggleOutputNegation(alias)
  else :
    if processAigerVariable(rhs1) in negated_gates :
      rhs1 = negateAigerLiteral(rhs1)
    if processAigerVariable(rhs2) in negated_gates :
      rhs2 = negateAigerLiteral(rhs2)
    
    if isNegatedAigerLiteral(rhs1) and isNegatedAigerLiteral(rhs2) :
      negated_gates.add(alias)
      if alias in pos_set :
        spec.toggleOutputNegation(alias)
      spec.addGateUnsorted(alias, [processAigerVariable(rhs1), processAigerVariable(rhs2)], bitarray.bitarray([0,1,1,1]))
    elif isNegatedAigerLiteral(rhs1) :
      spec.addGateUnsorted(alias, [processAigerVariable(rhs1), processAigerVariable(rhs2)], bitarray.bitarray([0,1,0,0]))
    elif isNegatedAigerLiteral(rhs2) :
      spec.addGateUnsorted(alias, [processAigerVariable(rhs1), processAigerVariable(rhs2)], bitarray.bitarray([0,0,1,0]))
    else :
      spec.addGateUnsorted(alias, [processAigerVariable(rhs1), processAigerVariable(rhs2)], bitarray.bitarray([0,0,0,1]))


def processAigerVariable(var) :
  return var // 2

def isNegatedAigerLiteral(lit) :
  return lit & 1

def negateAigerLiteral(lit) :
  return lit ^ 1

def processAigerLiteral(lit) :
  if isNegatedAigerLiteral(lit) :
    return -processAigerVariable(negateAigerLiteral(lit))
  else :
    return processAigerVariable(lit)

def getAigerVariable(var) :
  return 2 * var

def getAigerLiteral(lit) :
  if lit < 0 :
    return getAigerVariable(-lit) + 1
  else :
    return getAigerVariable(lit)