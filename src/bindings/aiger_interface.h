#ifndef AIGER_INTERFACE_H_
#define AIGER_INTERFACE_H_

#include <vector>
#include <string>
#include <tuple>
#include <iostream>

extern "C" {
    #include "aiger.h"
}

namespace circuit_synthesis {

class AigerInterface {

 public:
  AigerInterface();
  ~AigerInterface();

  bool writeAiger(const std::string& fname, bool binary_mode);
  void setInputs(const std::vector<int>& inputs);
  void setOutputs(const std::vector<int>& outputs);
  void addAnd(int in1,int in2, int out);

  void readAiger(const std::string& fname);
  std::vector<int> getInputs() const;
  std::vector<int> getOutputs() const;
  int getNofAnds() const;
  std::tuple<int,int,int> getAnd(int idx) const;

  int getConstantTrue() const;
  int getConstantFalse() const;

 private:
  aiger* circuit;
};

AigerInterface::AigerInterface() {
  circuit=aiger_init();
}

AigerInterface::~AigerInterface() {
  aiger_reset(circuit);
}

int AigerInterface::getConstantTrue() const {
  return aiger_true;
}

int AigerInterface::getConstantFalse() const {
  return aiger_false;
}

bool AigerInterface::writeAiger(const std::string& fname, bool binary_mode) {
  const char* msg=aiger_check(circuit);
  if (msg!=0) {
    std::cerr<<msg<<std::endl;
    return false;
  }
  FILE * file;
  file = fopen(fname.c_str(),"w");
  if(file==0) {
    std::cerr<<"File could not be opened."<<std::endl;
    return false;
  }
  int res;
  if (binary_mode) {
    res = aiger_write_to_file(circuit,aiger_binary_mode,file);
  } else {
    res = aiger_write_to_file(circuit,aiger_ascii_mode,file);
  }
  fclose(file);
  if (!res) {
    std::cerr<<"Could not write to file."<<std::endl;
    return false;
  }
  return true;
}

void AigerInterface::setInputs(const std::vector<int>& inputs) {
  for (int x : inputs) {
    aiger_add_input(circuit, x, nullptr);
  }
}

void AigerInterface::setOutputs(const std::vector<int>& outputs) {
  for (int x : outputs) {
    aiger_add_output(circuit, x, nullptr);
  }
}

void AigerInterface::addAnd(int in1,int in2, int out) {
  aiger_add_and(circuit, out, in1, in2);
}

void AigerInterface::readAiger(const std::string& fname) {
  aiger_open_and_read_from_file(circuit, fname.c_str());
}

std::vector<int> AigerInterface::getInputs() const {
  std::vector<int> inputs;
  inputs.reserve(circuit->num_inputs);
  for (int i=0;i<circuit->num_inputs;i++) {
    auto x = circuit->inputs[i];
    int var = x.lit&~1; //is this really necessary?
    inputs.push_back(var);
  }
  return inputs;
}

std::vector<int> AigerInterface::getOutputs() const {
  std::vector<int> outputs;
  outputs.reserve(circuit->num_outputs);
  for (int i=0;i<circuit->num_outputs;i++) {
    auto x = circuit->outputs[i];
    outputs.push_back(x.lit);
  }
  return outputs;
}

int AigerInterface::getNofAnds() const {
  return circuit->num_ands;
}

std::tuple<int,int,int> AigerInterface::getAnd(int idx) const {
  auto gate = circuit->ands[idx];
  return std::make_tuple(gate.lhs, gate.rhs0, gate.rhs1);
}


}


#endif // AIGER_INTERFACE_H_
