import pytest
from soteria.executor import Executor
from soteria.exceptions import BoogieParseError, BoogieTypeError, BoogieVerificationError
import os

class TestExecutor:
    def test_execute_boogie_parse_error(self):
        with pytest.raises(BoogieParseError):
            Executor.execute_boogie(None, 'type test;\n var a:test', 'name')

    def test_execute_boogie_type_error(self):
        with pytest.raises(BoogieTypeError):
            Executor.execute_boogie(None, 'type test;\n function check(one:test, two:test) returns(int)\n {one+two}', 'name')

    def test_execute_boogie_verification_error(self):
        with pytest.raises(BoogieVerificationError):
            Executor.execute_boogie(None, 'procedure F(n: int) returns (r: int) \n ensures r == 91; \n {  r := n; }', 'name')

    def test_execute_boogie_correct(self):
        result = Executor.execute_boogie(None, 'procedure F(n: int) returns (r: int)\n  ensures n == r;\n{  r := n;}')
        assert 'Boogie program verifier finished with 1 verified, 0 errors' in result

    def test_execute_boogie_verification_error_counter_model_created(self):
        try:
            Executor.execute_boogie(None, 'procedure F(n: int) returns (r: int) \n ensures r == 91; \n {  r := n; }', 'name')
        except Exception as e:
            pass
        assert os.path.isfile('results/name.model')
