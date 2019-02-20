from soteria.exceptions import SafetyError
from soteria.checks.safety_checker import SafetyChecker
from soteria.components.specification import Specification
from soteria.components.function import Function
from soteria.components.parameter import Parameter
from soteria.components.variable import Variable
from soteria.components.procedure import Procedure
import pytest

class TestSafetyChecker:
    def test_unsafe_proc(self):
        spec = Specification('sample')
        spec.add_variable(Variable('counter', 'int', 1))
        procedure = Procedure('dec', 15)
        procedure.add_parameter(Parameter('value', 'int'))
        procedure.add_modifies('counter')
        procedure.set_implementation('counter := counter - value;')
        spec.add_procedure(procedure)
        merge = Procedure('merge', 15)
        merge.add_parameter(Parameter('counter1', 'int'))
        merge.add_modifies('counter')
        merge.set_implementation('counter := (if counter1 > counter then counter1 else counter);')
        spec.set_merge(merge)
        invariant = Function('inv', 10)
        invariant.add_param(Parameter('counter', 'int'))
        invariant.set_return('bool')
        spec.set_invariant(invariant)
        spec.set_preface('var counter :int;\n//@invariant\nfunction inv(counter:int) returns(bool)\n{\n  counter >= 0\n}')
        checker = SafetyChecker()
        with pytest.raises(SafetyError):
            checker.check_safety(spec, procedure)

    def test_safe_proc(self):
        spec = Specification('sample')
        spec.add_variable(Variable('counter', 'int', 1))
        procedure = Procedure('inc', 15)
        procedure.add_parameter(Parameter('value', 'int'))
        procedure.add_modifies('counter')
        procedure.add_requires('value > 0')
        procedure.add_ensures('counter == old(counter) + value')
        procedure.set_implementation('counter := counter + value;')
        spec.add_procedure(procedure)
        merge = Procedure('merge', 15)
        merge.add_parameter(Parameter('counter1', 'int'))
        merge.add_modifies('counter')
        merge.set_implementation('counter := (if counter1 > counter then counter1 else counter);')
        spec.set_merge(merge)
        invariant = Function('inv', 10)
        invariant.add_param(Parameter('counter', 'int'))
        invariant.set_return('bool')
        spec.set_invariant(invariant)
        spec.set_preface('var counter :int;\n//@invariant\nfunction inv(counter:int) returns(bool)\n{\n  counter >= 0\n}')
        checker = SafetyChecker()
        assert checker.check_safety(spec, procedure) == True

    def test_unstable_pair(self):
        spec = Specification('sample')
        spec.add_variable(Variable('counter', 'int', 1))
        procedure = Procedure('dec', 15)
        procedure.add_parameter(Parameter('value', 'int'))
        procedure.add_modifies('counter')
        procedure.add_requires('counter > value')
        procedure.set_implementation('counter := counter - value;')
        spec.add_procedure(procedure)
        merge = Procedure('merge', 15)
        merge.add_parameter(Parameter('counter1', 'int'))
        merge.add_modifies('counter')
        merge.add_requires('counter > 0')
        merge.set_implementation('counter := (if counter1 > counter then counter1 else counter);')
        spec.set_merge(merge)
        invariant = Function('inv', 10)
        invariant.add_param(Parameter('counter', 'int'))
        invariant.set_return('bool')
        spec.set_invariant(invariant)
        spec.set_preface('var counter :int;\n//@invariant\nfunction inv(counter:int) returns(bool)\n{\n  counter >= 0\n}')
        checker = SafetyChecker()
        with pytest.raises(SafetyError):
            checker.check_stability(spec, procedure)

    def test_stable_pair(self):
        spec = Specification('sample')
        spec.add_variable(Variable('counter', 'int', 1))
        procedure = Procedure('inc', 15)
        procedure.add_parameter(Parameter('value', 'int'))
        procedure.add_modifies('counter')
        procedure.add_requires('value > 0')
        procedure.set_implementation('counter := counter + value;')
        spec.add_procedure(procedure)
        merge = Procedure('merge', 15)
        merge.add_parameter(Parameter('counter1', 'int'))
        merge.add_modifies('counter')
        merge.set_implementation('counter := (if counter1 > counter then counter1 else counter);')
        spec.set_merge(merge)
        invariant = Function('inv', 10)
        invariant.add_param(Parameter('counter', 'int'))
        invariant.set_return('bool')
        spec.set_invariant(invariant)
        spec.set_preface('var counter :int;\n//@invariant\nfunction inv(counter:int) returns(bool)\n{\n  counter >= 0\n}')
        checker = SafetyChecker()
        assert checker.check_stability(spec, procedure) == True
