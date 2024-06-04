#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "relationSynthesiser.h"

namespace py = pybind11;


PYBIND11_MODULE(relationSynthesiser, m) {
    py::class_<circuit_synthesis::Config>(m, "Configuration")
        .def(py::init<int, bool, bool, bool, bool, bool, bool, bool>());
    py::class_<circuit_synthesis::RelationSynthesiser>(m, "RelationSynthesiser")
        .def(py::init<const circuit_synthesis::booleanRelation&, const std::vector<std::pair<int,int>>&, const std::vector<int>&, const std::vector<int>&, int, const circuit_synthesis::Config>())
        .def("checkSize", py::overload_cast<unsigned int>(&circuit_synthesis::RelationSynthesiser::checkSize))
        .def("checkSizeTO", py::overload_cast<unsigned int, double>(&circuit_synthesis::RelationSynthesiser::checkSize))
        .def("getModel", &circuit_synthesis::RelationSynthesiser::getModel)
        .def("toggleNoReapplicationRule", &circuit_synthesis::RelationSynthesiser::toggleNoReapplicationRule)
        .def("getSelectionVariables", &circuit_synthesis::RelationSynthesiser::getSelectionVariables, py::return_value_policy::reference_internal)
        .def("getDefinitionVariables", &circuit_synthesis::RelationSynthesiser::getDefinitionVariables, py::return_value_policy::reference_internal)
        .def("getOutputVariables", &circuit_synthesis::RelationSynthesiser::getOutputVariables, py::return_value_policy::reference_internal);

}