#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Sep  2 15:35:54 2022

"""

from bitarray.util import int2ba

def getClausalEncodingUnique(gate, unique_bit=True):
  # Bespoke encoding for AND (unique_bit=True) and OR gates (unique_bit=False).
  v = gate.getAlias()
  i = gate.table.index(unique_bit)
  tt_line = int2ba(i, length=len(gate.inputs))
  assignment_unique = [w if polarity else -w 
                       for w, polarity in zip(gate.inputs, tt_line)]
  long_clause = [-w for w in assignment_unique] + [v if unique_bit else -v]
  small_clauses = [[w, -v if unique_bit else v] for w in assignment_unique]
  return small_clauses + [long_clause]

def getNaiveClausalEncoding(gate):
  v = gate.getAlias()
  clauses = []
  for i, o in enumerate(gate.table):
    tt_line = int2ba(i, length=len(gate.inputs))
    clause = [-w if polarity else w 
              for w, polarity in zip(gate.inputs, tt_line)] + [v if o else -v]
    clauses.append(clause)
  return clauses

def getClausalEncodingGate(gate):
  v = gate.getAlias()
  # s = sum(gate.table)
  s = gate.table.count()
  if s == 0:
    return [[-v]]
  elif s == len(gate.table):
    return [[v]]
  elif s == 1:
    return getClausalEncodingUnique(gate, True)
  elif s == len(gate.table) - 1:
    return getClausalEncodingUnique(gate, False)
  else:
    return getNaiveClausalEncoding(gate)

def getClausalEncodingSpec(spec, gate_aliases=None):
  if gate_aliases is None:
    aliases_to_consider = spec.getGateAliases()
  else :
    aliases_to_consider = gate_aliases
  return [clause for alias in aliases_to_consider for clause in getClausalEncodingGate(spec.getGate(alias))]

def getVariables(clauses):
  return {abs(l) for clause in clauses for l in clause}

def getRenaming(variables, renamed_range_start=None):
  if renamed_range_start is None:
    renamed_range_start = max(variables) + 1
  return {w: v for v, w in enumerate(variables, start=renamed_range_start)}

def getRenamedLiteral(l, renaming):
  v = abs(l)
  w = renaming.get(v, v)
  return w if l > 0 else -w

def getRenamedClause(clause, renaming):
  return [getRenamedLiteral(l, renaming) for l in clause]

def getRenamedClauses(clauses, renaming):
  return [getRenamedClause(clause, renaming) for clause in clauses]

def getRenamingAndClauses(clauses, renamed_range_start=None, taboo=None):
  taboo = set() if taboo is None else set(taboo)
  variables_to_rename = {v for v in getVariables(clauses) if v not in taboo}
  renaming = getRenaming(variables_to_rename, renamed_range_start)
  return getRenamedClauses(clauses, renaming), renaming

def getEqualityClauses(x, y, auxiliary):
  return [[x, -y, -auxiliary], [-x, y, -auxiliary],
          [x, y, auxiliary], [-x, -y, auxiliary]]
  