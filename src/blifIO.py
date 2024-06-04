import bitarray

from specification import Specification
from utils import isNormalised
from utils import negateTable
from utils import getBitSeq

# ordered_blif: the gates are ordered topologically
def getSpecification(fname, ordered_blif=False) :
  parser = BlifParser()
  return parser.parse(fname, ordered_blif)

def writeSpecification(fname, spec, spec_name = "spec") :
  with open(fname,"w") as file: 
    writeSpecification2Stream(file, spec, spec_name)

def getAuxNodeAlias(counter) :
  return f"_aux_{counter}_"

# TODO: Write input-outputs as projections (as other tools do)
def setOutputs(out, spec, outputs_in_both_polarities) :
  out_str = []
  outputs = spec.getOutputs()
  inputs = set(spec.getInputs())
  max_var = spec.max_var
  aux_var_dict = {x : max_var + idx + 1 for idx,x in enumerate(outputs_in_both_polarities) }
  max_var += len(outputs_in_both_polarities)
  str_to_append = ""
  for idx, o in enumerate(outputs) :
    if o in inputs :
      if spec.isOutputNegated(idx) :
        max_var += 1
        str_to_append += f".names {o} {max_var}\n"
        str_to_append += "0 1\n"
        out_str.append(str(max_var))
      else :
        out_str.append(str(o))
    elif o in outputs_in_both_polarities and spec.isOutputNegated(idx) :
      out_str.append(str(aux_var_dict[o]))
    else :
      out_str.append(str(o))
  seen = set()
  counter = 1
  alias_association = {}
  for idx, o in enumerate(out_str) :
    if o in seen :
      newAlias = getAuxNodeAlias(counter)
      alias_association[newAlias] = o
      out_str[idx] = newAlias
      counter += 1
    else :
      seen.add(o)
  out.write(".outputs " + " ".join(out_str) + "\n")
  out.write(str_to_append)
  for new_alias, old_alias  in alias_association.items() :
    out.write(f".names {old_alias} {new_alias}\n")
    out.write("1 1\n")
  return aux_var_dict


def writeSpecification2Stream(out, spec, spec_name = "spec") :
  out.write(f".model {spec_name}\n")
  out.write(".inputs " + " ".join(str(x) for x in spec.getInputs()) + "\n")

  # The specifications are always normalised, this means that outputs may need to be negated in order to get a representation for the original circuit.
  # A gate may represent multiple outputs. 
  # It is possible that a single gate represents both an output that needs to be negated and another one that does not.
  # For this reason we introduce two different gates for such gates, one representing the negation and one the original gate.
  negated_outputs, outputs_in_both_polarities = spec.getOutputsToNegate()
  negated_outputs.difference_update(spec.pis)
  aux_var_dict = setOutputs(out, spec, outputs_in_both_polarities)
  for gate in spec.orderedGateTraversal() :

    alias = gate.getAlias()
    table = gate.table.copy()
    inputs = gate.inputs
    if alias in negated_outputs :
      table = negateTable(table)
      writeBlifGate(out, alias, table, inputs, negated_outputs)
    elif alias in outputs_in_both_polarities :
      writeBlifGate(out, alias, table, inputs, negated_outputs)
      alias_negated = aux_var_dict[alias]
      writeBlifGate(out, alias_negated, bitarray.bitarray([1,0]), [alias], negated_outputs)
    else :
      writeBlifGate(out, alias, table, inputs, negated_outputs)
  
  out.write(".end\n")

def writeBlifGate(file, alias, table, inputs, negated_gates) :
  file.write(".names " + " ".join(str(x) for x in inputs) + " " + str(alias) + "\n")
  negated_inputs_indices = {idx for idx, var in enumerate(inputs) if var in negated_gates}
  for idx, val in enumerate(table) :
    if val == 1 :
      binary_representation = [x ^ 1 if idx in negated_inputs_indices else x for idx, x in enumerate(getBitSeq(idx, len(inputs)))]
      file.write("".join(str(x) for x in binary_representation) + " 1\n")




class BlifParser :

  class InvalidBlifException(Exception):
    pass

  # def __init__(self) :
  #   pass

  def parse(self, fname, ordered_blif) :
    self.max_var = 0
    self.alias_renaming = {}
    self.alias_names = set()
    with open(fname,"r") as file: 
      inputs, outputs = self.readBlifIO(file)
      spec_builder = SpecificationBuilder(inputs, outputs, ordered_blif)
      self.readGates(spec_builder, file)
    return spec_builder.getSpecification()

  def readGates(self, spec_builder, file) :
    line = self.getLine(file)
    gate_lines = None
    while line :
      if line.startswith("#") :
        line = self.getLine(file)
        continue
      if line.startswith(".names") : # new gate
        if not gate_lines is None :
          self.addGate(spec_builder, gate_alias, inputs, gate_lines, output_value)
        inputs, gate_alias = self.parseGateHeader(line)
        gate_lines = []
        output_value = None
      elif line.startswith(".end") :
        if not gate_lines is None : # needed as there could be no gate
          self.addGate(spec_builder, gate_alias, inputs, gate_lines, output_value)
      else :
        x = line.split()
        output = int(x[-1])
        if not output_value is None and output != output_value :
          raise BlifParser.InvalidBlifException(f"Gate {gate_alias}: non unique output plane")
        if output_value is None :
          output_value = output
        if len(inputs) > 0 :
          assert len(x) == 2, "Lines must consist of an input and an output assignment"
          lits = [-1 if x=="-" else int(x) for x in x[0]]
          gate_lines += [lits]
      line = self.getLine(file)

  def getLine(self, file) :
    line = file.readline()
    while not line.strip() and len(line) > 0 :
      line = file.readline()
    while line.endswith("\\\n") :
      line = line.rstrip("\\\n")
      x = file.readline()
      line += x
    return line.lstrip()

  def readBlifIO(self, file) :
    inputs = []
    outputs = []
    line = self.getLine(file)
    while line :
      if line.startswith(".inputs") :
        input_str = line.split()
        inputs += [self.getAlias(x) for x in input_str[1:]]
      elif line.startswith(".outputs") :
        output_str = line.split()
        outputs += [self.getAlias(x) for x in output_str[1:]]
      # elif not line.startswith("#") and not line.startswith(".model") :
      #   break
      pos = file.tell()
      line = self.getLine(file)
      if line.startswith(".names") :
        file.seek(pos)
        break


    if len(inputs) == 0 :
      print("Warning: Constant circuit given.")
      # raise BlifParser.InvalidBlifException("No inputs given")
    if len(outputs) == 0 :
      raise BlifParser.InvalidBlifException("No outputs given")

    return inputs, outputs

  def getAlias(self, x) :
    if x in self.alias_renaming :
      return self.alias_renaming[x]
    try :
      alias = int(x)
      if alias in self.alias_names :
        self.max_var += 1
        alias = self.max_var
      else :
        self.max_var = max(self.max_var, alias)
    except :
      self.max_var += 1
      alias = self.max_var
    self.alias_names.add(alias)
    self.alias_renaming[x] = alias
    return alias

  def parseGateHeader(self, line) :
    in_str = line.split()[1:-1]
    out_str = line.split()[-1]
    return [self.getAlias(y) for y in in_str], self.getAlias(out_str)

  def addGate(self, spec_builder, alias, inputs, gate_lines, output_value) :
    assert not output_value is None or len(gate_lines) == 0 , "If there are gate lines there must be an output value"
    default_output_value = 0
    if output_value is None :
      val = default_output_value
    else :
      val = output_value
    spec_builder.addGate(alias, inputs, gate_lines, val)




class SpecificationBuilder :

  def __init__(self, pis, pos, gates_topologoically_ordered = False) :
    self.specification = Specification(pis, pos)
    self.negated_gates = set()
    self.pos_set = set(pos)
    self.gates_topologoically_ordered = gates_topologoically_ordered


  # In a blif gate the lines describing the gate can either determine the input combinations 
  # where the gate is true (output_value = True) or false (output_value = False)
  def addGate(self, gate_alias, inputs, lines, output_value) :
    table = self.getTableFromGate(lines, inputs, output_value)
    if len(table) == 0 :
      inputs = []
    if not isNormalised(table) :
      self.negated_gates.add(gate_alias)
      table = negateTable(table)
      if gate_alias in self.pos_set :
        self.specification.negateOutput(gate_alias)
    if self.gates_topologoically_ordered :
      self.specification.addGate(gate_alias, inputs, table)
    else :
      self.specification.addGateUnsorted(gate_alias, inputs, table)


  # The method takes a blif like representation of a gate.
  # If output_value is false, then defining table contains all the input combination for which the gate
  # shall be false -- respectively true if negated is true. 
  # inputs_to_negate contains the indices of the gates that need to be negated
  # It returns a list with 2^k inputs where k is the number of inputs of the gate -- unless the gate is constant.
  # The ith entry in the resulting table is 1 iff the ith line in the truth table 
  # representing the given table is 1.
  def getTableFromGate(self, lines, inputs, output_value) :
    # Either describe the input combination where the gate is positive or where it is negative
    # specify_positively = len([x for x in table if x > 0]) <= (2 ** (len(inputs) - 1))
    if len(lines) == 0 or len(lines[0]) == 0 :
      if output_value :
        return bitarray.bitarray([1])
      else :
        return bitarray.bitarray([0])
    input_indices_to_negate = set(i for i,x  in enumerate(inputs) if x in self.negated_gates)
    nof_inputs = len(lines[0])
    # if negated is true the default value is 1 -- only if there is a line in the table the output is 0.
    # table = [1 if negated else 0 for _ in range(2 ** nof_inputs)]
    table = bitarray.bitarray([0 if output_value else 1 for _ in range(2 ** nof_inputs)])
    for line in lines :
      to_set = [0] # the positions in the table that need to be considered
      for idx, lit in enumerate(line) :
        if idx in input_indices_to_negate :
          lit = lit ^ 1
        # remember the ordering of the tables
        reversed_idx = nof_inputs - 1 - idx
        # arbitrary assignment of literal
        # if there is dont't care literal in a line we have to set more than one entry in the tables
        if lit < 0 : 
          to_set += [x + (2 ** reversed_idx) for x in to_set]
        elif lit == 1 : # positive literal
          to_set = [x + (2 ** reversed_idx) for x in to_set]

      for idx in to_set:
        table[idx] = 1 if output_value else 0
    return table

  def getSpecification(self) :
    self.specification.init(self.gates_topologoically_ordered)
    return self.specification

