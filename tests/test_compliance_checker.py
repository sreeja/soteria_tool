import pytest
from mock import Mock, patch
from soteria.checks.compliance_checker import ComplianceChecker
from soteria.components.specification import Specification
from soteria.components.function import Function
from soteria.components.parameter import Parameter
from soteria.exceptions import ComplianceError
from soteria.components.variable import Variable
from soteria.components.procedure import Procedure

class TestComplianceChecker:
    def test_check_merge_merge_not_defined(self):
        variables = []
        merge = ''
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_merge(merge, variables)

    def test_check_invariant_invariant_not_defined(self):
        invariant = None
        variables = []
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_invariant(invariant, variables)

    def test_check_invariant_different_number_parameters(self):
        invariant = Function('inv', 2)
        invariant.parameters = []
        invariant.parameters.append(Parameter('t1', 'int'))
        variables = []
        variables.append(Variable('t1','int', 10))
        variables.append(Variable('t2','bool', 11))
        invariant.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_invariant(invariant, variables)

    def test_check_invariant_global_var_diff_datatype(self):
        invariant = Function('inv', 2)
        invariant.parameters = []
        invariant.parameters.append(Parameter('t1', 'int'))
        invariant.parameters.append(Parameter('t2', 'bool'))
        variables = []
        variables.append(Variable('t1','int', 10))
        variables.append(Variable('t2','int', 11))
        invariant.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_invariant(invariant, variables)

    def test_check_invariant_global_var_diff_name(self):
        invariant = Function('inv', 2)
        invariant.parameters = []
        invariant.parameters.append(Parameter('t1', 'int'))
        invariant.parameters.append(Parameter('t12', 'bool'))
        variables = []
        variables.append(Variable('t1','int', 10))
        variables.append(Variable('t2','bool', 11))
        invariant.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_invariant(invariant, variables)

    def test_check_invariant_return_datatype_bool(self):
        invariant = Function('inv', 2)
        invariant.parameters = []
        invariant.parameters.append(Parameter('t1', 'int'))
        invariant.parameters.append(Parameter('t2', 'bool'))
        variables = []
        variables.append(Variable('t1','int', 10))
        variables.append(Variable('t2','bool', 11))
        invariant.returndt = 'int'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_invariant(invariant, variables)

    def test_check_invariant_compliant_invariant(self):
        invariant = Function('inv', 2)
        invariant.parameters = []
        invariant.parameters.append(Parameter('t1', 'int'))
        invariant.parameters.append(Parameter('t2', 'bool'))
        variables = []
        variables.append(Variable('t1','int', 10))
        variables.append(Variable('t2','bool', 11))
        invariant.returndt = 'bool'
        checker = ComplianceChecker()
        assert checker.check_invariant(invariant, variables) == True

    def test_check_gteq_compliant_gteq(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        variables.append(Variable('two', 'TestType', 13))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.parameters.append(Parameter('two1', 'TestType'))
        gteq.parameters.append(Parameter('two2', 'TestType'))
        gteq.returndt = 'bool'
        checker = ComplianceChecker()
        assert checker.check_gteq(gteq, variables) == True
    
    def test_check_gteq_no_gteq_defined(self):
        variables=[]
        variables.append(Variable('four', 'TestType', 13))
        gteq = None
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_gteq_odd_parameter_number(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        variables.append(Variable('two', 'TestType', 13))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.parameters.append(Parameter('two1', 'TestType'))
        gteq.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_gteq_diff_parameter_number_less(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        variables.append(Variable('two', 'TestType', 13))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_gteq_diff_parameter_number_more(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.parameters.append(Parameter('two1', 'TestType'))
        gteq.parameters.append(Parameter('two2', 'TestType'))
        gteq.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_gteq_returndt_not_bool(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        variables.append(Variable('two', 'TestType', 13))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.parameters.append(Parameter('two1', 'TestType'))
        gteq.parameters.append(Parameter('two2', 'TestType'))
        gteq.returndt = 'int'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_gteq_datatypes_different(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        variables.append(Variable('two', 'TestType', 13))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.parameters.append(Parameter('two1', 'int'))
        gteq.parameters.append(Parameter('two2', 'int'))
        gteq.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_gteq_not_all_variables_present(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        variables.append(Variable('two', 'TestType', 13))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.parameters.append(Parameter('too1', 'TestType'))
        gteq.parameters.append(Parameter('too2', 'TestType'))
        gteq.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_gteq_naming_convention1(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        variables.append(Variable('two', 'TestType', 13))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one_1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.parameters.append(Parameter('two1', 'TestType'))
        gteq.parameters.append(Parameter('two2', 'TestType'))
        gteq.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_gteq_naming_convention2(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        variables.append(Variable('two', 'TestType', 13))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one_2', 'int'))
        gteq.parameters.append(Parameter('two1', 'TestType'))
        gteq.parameters.append(Parameter('two2', 'TestType'))
        gteq.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_gteq_datatype_not_paired(self):
        variables=[]
        variables.append(Variable('one', 'int', 10))
        variables.append(Variable('two', 'TestType', 13))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.parameters.append(Parameter('two1', 'int'))
        gteq.parameters.append(Parameter('two2', 'TestType'))
        gteq.returndt = 'bool'
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_gteq(gteq, variables)

    def test_check_merge_compliant(self):
        variables = []
        variables.append(Variable('one', 'int', 4))
        variables.append(Variable('two', 'bool', 4))
        merge = Procedure('merge_proc', 10)
        merge.add_parameter(Parameter('one1', 'int'))
        merge.add_parameter(Parameter('two1', 'bool'))
        merge.add_modifies('one')
        merge.add_modifies('two')
        checker = ComplianceChecker()
        assert checker.check_merge(merge, variables) == True

    def test_check_merge_param_number_less(self):
        variables = []
        variables.append(Variable('one', 'int', 4))
        variables.append(Variable('two', 'bool', 4))
        merge = Procedure('merge_proc', 10)
        merge.add_parameter(Parameter('one1', 'int'))
        merge.add_modifies('one')
        merge.add_modifies('two')
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_merge(merge, variables)

    def test_check_merge_modifies_number_less(self):
        variables = []
        variables.append(Variable('one', 'int', 4))
        variables.append(Variable('two', 'bool', 4))
        merge = Procedure('merge_proc', 10)
        merge.add_parameter(Parameter('one1', 'int'))
        merge.add_parameter(Parameter('two1', 'bool'))
        merge.add_modifies('two')
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_merge(merge, variables)

    # def test_check_merge_same_datatype_params(self):
    #     variables = []
    #     variables.append(Variable('one', 'int', 4))
    #     variables.append(Variable('two', 'int', 4))
    #     merges = []
    #     merge = Procedure('merge_proc', 10)
    #     merge.add_parameter(Parameter('p1', 'int'))
    #     merge.add_parameter(Parameter('p2', 'int'))
    #     merge.add_modifies('one')
    #     merge.add_modifies('two')
    #     merges.append(merge)
    #     checker = ComplianceChecker()
    #     with pytest.raises(ComplianceError):
    #         checker.check_merge(merges, variables)

    def test_check_merge_modifies_param_datatype_match(self):
        variables = []
        variables.append(Variable('one', 'int', 4))
        variables.append(Variable('two', 'bool', 4))
        merge = Procedure('merge_proc', 10)
        merge.add_parameter(Parameter('one1', 'int'))
        merge.add_parameter(Parameter('two1', 'real'))
        merge.add_modifies('one')
        merge.add_modifies('two')
        checker = ComplianceChecker()
        with pytest.raises(ComplianceError):
            checker.check_merge(merge, variables)

    # def test_check_merge_modifies_param_no_match(self):
    #     variables = []
    #     variables.append(Variable('one', 'int', 4))
    #     variables.append(Variable('two', 'bool', 4))
    #     merges = []
    #     merge = Procedure('merge_proc', 10)
    #     merge.add_parameter(Parameter('p1', 'int'))
    #     merge.add_parameter(Parameter('p2', 'real'))
    #     merge.add_modifies('one')
    #     merge.add_modifies('three')
    #     merges.append(merge)
    #     checker = ComplianceChecker()
    #     with pytest.raises(ComplianceError):
    #         checker.check_merge(merges, variables)

    def get_compliant_spec(self):
        spec = Specification('name')
        spec.add_variable(Variable('one', 'int', 4))
        gteq = Function('gteq', 2)
        gteq.parameters.append(Parameter('one1', 'int'))
        gteq.parameters.append(Parameter('one2', 'int'))
        gteq.returndt = 'bool'
        spec.set_gteq(gteq)
        inv = Function('inv', 2)
        inv.returndt = 'bool'
        inv.parameters.append(Parameter('one', 'int'))
        spec.set_invariant(inv)
        merge = Procedure('merge_proc', 10)
        merge.add_parameter(Parameter('one1', 'int'))
        merge.add_modifies('one')
        spec.set_merge(merge)
        return spec

    @patch('soteria.checks.compliance_checker.ComplianceChecker.check_merge')
    def test_check_check_merge_called(self, mock):
        checker = ComplianceChecker()
        spec = self.get_compliant_spec()
        checker.check(spec)
        assert mock.called == True

    @patch('soteria.checks.compliance_checker.ComplianceChecker.check_gteq')
    def test_check_check_gteq_called(self, mock):
        checker = ComplianceChecker()
        spec = self.get_compliant_spec()
        checker.check(spec)
        assert mock.called == True

    @patch('soteria.checks.compliance_checker.ComplianceChecker.check_invariant')
    def test_check_check_invariant_called(self, mock):
        checker = ComplianceChecker()
        spec = self.get_compliant_spec()
        checker.check(spec)
        assert mock.called == True