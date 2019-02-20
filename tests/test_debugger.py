from soteria.debug_support.debugger import Debugger
from soteria.components.procedure import Procedure
from soteria.components.parameter import Parameter

class TestDebugger:

    message = '''Boogie program verifier version 2.3.0.61016, Copyright (c) 2003-2014, Microsoft.
test_models/stability_decrement_transfer.bpl(167,1): Error BP5002: A precondition for this call might not hold.
test_models/stability_decrement_transfer.bpl(145,1): Related location: This is the precondition that might not hold.
Execution trace:
    test_models/stability_decrement_transfer.bpl(163,2): anon0

Boogie program verifier finished with 2 verified, 1 error'''

    def test_get_parameters(self):
        debugger = Debugger()
        proc1 = Procedure('test', 15)
        proc1.add_parameter(Parameter('param1', 'int'))
        proc1.add_parameter(Parameter('param2', 'bool'))
        procs = []
        procs.append(proc1)
        params = debugger.get_parameters(procs)
        assert len(params) == 2
        assert 'param1' in params
        assert 'param2' in params

    def test_get_failed_expression(self):
        debugger = Debugger()
        spec_file = open('tests/test_models/stability_decrement_transfer.bpl')
        test_spec = spec_file.readlines()
        errors = debugger.get_failures(test_spec, self.message)
        assert len(errors) == 1
        assert errors[0].expression == 'call transfer(_from1,_to1,_n1);'
        assert errors[0].related_locations[0].expression == 'requires (local_rights(from, R, U) >= n);'

    def test_get_debug_info(self):
        #for now only param values
        debugger = Debugger()
        procs = []
        proc1 = Procedure('decrement', 130)
        proc1.add_parameter(Parameter('id', 'int'))
        proc1.add_parameter(Parameter('n', 'int'))
        procs.append(proc1)
        proc2 = Procedure('transfer', 141)
        proc2.add_parameter(Parameter('from', 'int'))
        proc2.add_parameter(Parameter('to', 'int'))
        proc2.add_parameter(Parameter('n', 'int'))
        procs.append(proc2)
        spec_file = open('tests/test_models/stability_decrement_transfer.bpl')
        test_spec = spec_file.readlines()
        info = debugger.get_debug_info(procs, test_spec, self.message, 'tests/test_models/stability_decrement_transfer.model')
        assert '''A precondition for this call might not hold.
call transfer(_from1,_to1,_n1);
This is the precondition that might not hold.
requires (local_rights(from, R, U) >= n);
The value of parameters and variables are ::''' in info
        assert '_id0 -> 88' in info
        assert '_n0 -> 1188' in info
        assert '_n1 -> 6270' in info
        assert '_from1 -> 88' in info
        assert '_to1 -> 87' in info