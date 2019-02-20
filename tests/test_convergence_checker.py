import pytest
from mock import Mock, patch
from soteria.checks.convergence_checker import ConvergenceChecker
from soteria.exceptions import ConvergenceError
from soteria.components.specification import Specification
from soteria.components.variable import Variable
from soteria.components.procedure import Procedure
from soteria.components.parameter import Parameter
from soteria.components.function import Function

class TestConvergenceChecker:
    def test_check_not_monotonicity(self):
        spec = Specification('sample')
        spec.add_variable(Variable('set', '[int]bool', 1))
        procedure = Procedure('remove', 15)
        procedure.add_parameter(Parameter('value', 'int'))
        procedure.add_modifies('set')
        procedure.set_implementation('set[value] := false;')
        spec.add_procedure(procedure)
        gteq = Function('gteq', 5)
        gteq.add_param(Parameter('one', '[int]bool'))
        gteq.add_param(Parameter('two', '[int]bool'))
        gteq.set_return('bool')
        spec.set_gteq(gteq)
        spec.set_preface('var set:[int]bool;\n//@gteq\nfunction gteq(set1:[int]bool, set2:[int]bool) returns(bool)\n{(forall i:int :: set2[i] ==> set1[i])}')
        checker = ConvergenceChecker()
        with pytest.raises(ConvergenceError):
            checker.check_monotonicity(spec, procedure)

    def test_check_monotonicity(self):
        spec = Specification('sample')
        spec.add_variable(Variable('set', '[int]bool', 1))
        procedure = Procedure('add', 15)
        procedure.add_parameter(Parameter('value', 'int'))
        procedure.add_modifies('set')
        procedure.add_ensures('(forall i:int :: (i == value ==> set[i] == true) && (i != value ==> set[i] == old(set)[i]))')
        procedure.set_implementation('set[value] := true;')
        spec.add_procedure(procedure)
        gteq = Function('gteq', 5)
        gteq.add_param(Parameter('set1', '[int]bool'))
        gteq.add_param(Parameter('set2', '[int]bool'))
        gteq.set_return('bool')
        spec.set_gteq(gteq)
        spec.set_preface('var set:[int]bool;\n//@gteq\nfunction gteq(set1:[int]bool, set2:[int]bool) returns(bool)\n{(forall i:int :: set2[i] ==> set1[i])}')
        checker = ConvergenceChecker()
        assert checker.check_monotonicity(spec, procedure) == True

    def test_check_not_lub(self):
        spec = Specification('sample')
        spec.add_variable(Variable('set', '[int]bool', 1))
        procedure = Procedure('merge_4', 15)
        procedure.add_parameter(Parameter('set1', '[int]bool'))
        procedure.add_modifies('set')
        procedure.add_ensures('(forall i:int :: set[i] == set1[i])')
        procedure.set_implementation('assume false;')
        spec.set_merge(procedure)
        gteq = Function('gteq', 5)
        gteq.add_param(Parameter('set1', '[int]bool'))
        gteq.add_param(Parameter('set2', '[int]bool'))
        gteq.set_return('bool')
        spec.set_gteq(gteq)
        spec.set_preface('var set:[int]bool;\n//@gteq\nfunction gteq(set1:[int]bool, set2:[int]bool) returns(bool)\n{(forall i:int :: set2[i] ==> set1[i])}')
        checker = ConvergenceChecker()
        with pytest.raises(ConvergenceError):
            checker.check_lub(spec)

    def test_check_ub_not_least(self):
        spec = Specification('sample')
        spec.add_variable(Variable('set', '[int]bool', 1))
        procedure = Procedure('merge_5', 15)
        procedure.add_parameter(Parameter('set1', '[int]bool'))
        procedure.add_modifies('set')
        procedure.add_ensures('(forall i:int :: set[i] == true)')
        procedure.set_implementation('assume false;')
        spec.set_merge(procedure)
        gteq = Function('gteq', 5)
        gteq.add_param(Parameter('set1', '[int]bool'))
        gteq.add_param(Parameter('set2', '[int]bool'))
        gteq.set_return('bool')
        spec.set_gteq(gteq)
        spec.set_preface('var set:[int]bool;\n//@gteq\nfunction gteq(set1:[int]bool, set2:[int]bool) returns(bool)\n{(forall i:int :: set2[i] ==> set1[i])}')
        checker = ConvergenceChecker()
        with pytest.raises(ConvergenceError):
            checker.check_lub(spec)

    def test_check_lub(self):
        spec = Specification('sample')
        spec.add_variable(Variable('set', '[int]bool', 1))
        procedure = Procedure('merge_6', 15)
        procedure.add_parameter(Parameter('set1', '[int]bool'))
        procedure.add_modifies('set')
        procedure.add_ensures('(forall i:int :: set[i] == (old(set)[i] || set1[i]))')
        procedure.set_implementation('assume false;')
        spec.set_merge(procedure)
        gteq = Function('gteq', 5)
        gteq.add_param(Parameter('set1', '[int]bool'))
        gteq.add_param(Parameter('set2', '[int]bool'))
        gteq.set_return('bool')
        spec.set_gteq(gteq)
        spec.set_preface('var set:[int]bool;\n//@gteq\nfunction gteq(set1:[int]bool, set2:[int]bool) returns(bool)\n{(forall i:int :: set2[i] ==> set1[i])}')
        checker = ConvergenceChecker()
        assert checker.check_lub(spec) == True

    def get_spec(self):
        spec = Specification('sample')
        spec.add_variable(Variable('set', '[int]bool', 1))
        procedure = Procedure('merge_6', 15)
        procedure.add_parameter(Parameter('set1', '[int]bool'))
        procedure.add_modifies('set')
        procedure.add_ensures('(forall i:int :: set[i] == (old(set)[i] || set1[i]))')
        procedure.set_implementation('assume false;')
        spec.set_merge(procedure)
        gteq = Function('gteq', 5)
        gteq.add_param(Parameter('set1', '[int]bool'))
        gteq.add_param(Parameter('set2', '[int]bool'))
        gteq.set_return('bool')
        spec.set_gteq(gteq)
        spec.set_preface('var set:[int]bool;\n//@gteq\nfunction gteq(set1:[int]bool, set2:[int]bool) returns(bool)\n{(forall i:int :: set2[i] ==> set1[i])}')
        procedure = Procedure('add', 15)
        procedure.add_parameter(Parameter('value', 'int'))
        procedure.add_modifies('set')
        procedure.add_ensures('(forall i:int :: (i == value ==> set[i] == true) && (i != value ==> set[i] == old(set)[i]))')
        procedure.set_implementation('set[value] := true;')
        spec.add_procedure(procedure)
        return spec

    @patch('soteria.checks.convergence_checker.ConvergenceChecker.check_monotonicity')
    def test_check_check_monotonicity_called(self, mock):
        checker = ConvergenceChecker()
        spec = self.get_spec()
        checker.check(spec)
        assert mock.called == True

    @patch('soteria.checks.convergence_checker.ConvergenceChecker.check_lub')
    def test_check_check_lub_called(self, mock):
        checker = ConvergenceChecker()
        spec = self.get_spec()
        checker.check(spec)
        assert mock.called == True