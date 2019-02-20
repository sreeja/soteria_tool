import pytest
from mock import Mock
from soteria.checks.syntax_checker import SyntaxChecker
from soteria.exceptions import EmptyInputError, BoogieParseError

class TestSyntaxChecker:
    def test_check_empty_name(self):
        checker = SyntaxChecker()
        with pytest.raises(EmptyInputError):
            checker.check('', '')

    def test_comment_annotations_annotations(self):
        checker = SyntaxChecker()
        spec = []
        spec.append('@test')
        assert '//@test' == checker._comment_annotations(spec)[0]

    # def test_check_raise_BoogieSyntaxError(self):
    #     #from soteria.executor import Executor
    #     import soteria

    #     import ipdb
    #     ipdb.set_trace()
    #     soteria.executor.Executor.execute_boogie = Mock(side_effect=BoogieParseError)
    #     checker = SyntaxChecker()
    #     spec = []
    #     spec.append('type a = int')
    #     with pytest.raises(BoogieParseError):
    #         checker.check('name', spec)

    # def test_check_correct(self, monkeypatch):
    #     #from soteria.executor import Executor
    #     import soteria
    #     import ipdb
    #     ipdb.set_trace()

    #     soteria.executor.Executor.execute_boogie = Mock(return_value='pass')
    #     checker = SyntaxChecker()
    #     assert 'pass' == checker.check('name', 'type a;')
