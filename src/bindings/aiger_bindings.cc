#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <vector>

#include "aiger_interface.h"

namespace py = pybind11;

PYBIND11_MODULE(aiger, m) {
    py::class_<circuit_synthesis::AigerInterface>(m, "Aiger")
        .def(py::init<>())
        .def("writeAiger", &circuit_synthesis::AigerInterface::writeAiger)
        .def("setInputs", &circuit_synthesis::AigerInterface::setInputs)
        .def("setOutputs", &circuit_synthesis::AigerInterface::setOutputs)
        .def("addAnd", &circuit_synthesis::AigerInterface::addAnd)
        .def("readAiger", &circuit_synthesis::AigerInterface::readAiger)
        .def("getInputs", &circuit_synthesis::AigerInterface::getInputs)
        .def("getOutputs", &circuit_synthesis::AigerInterface::getOutputs)
        .def("getNofAnds", &circuit_synthesis::AigerInterface::getNofAnds)
        .def("getAnd", &circuit_synthesis::AigerInterface::getAnd)
        .def("getConstantTrue", &circuit_synthesis::AigerInterface::getConstantTrue)
        .def("getConstantFalse", &circuit_synthesis::AigerInterface::getConstantFalse);
}


