# import pytest
# from soteria.verifier import Verifier
# from soteria.exceptions import *
# from soteria.checks.safety_checker import SafetyChecker
# from soteria.checks.compliance_checker import ComplianceChecker
# from soteria.checks.convergence_checker import ConvergenceChecker
# from mock import patch

# class TestVerifier:
#     #sanity checks
#     def test_analyze_spec_path_empty(self):
#         verifier = Verifier()
#         assert verifier.analyze('') == False

#     def test_analyze_spec_file_other_ending(self):
#         verifier = Verifier()
#         assert verifier.analyze('/spec_file.abc') == False

#     def test_analyze_error_in_spec_file_read(self):
#         verifier = Verifier()
#         assert verifier.analyze('/not_a_file.spec') == False

#     def test_get_specificaiton_name(self):
#         verifier = Verifier()
#         assert 'name' == verifier.get_specification_name('./test/test_specs/name.spec')

#     #syntax issues
#     def test_analyze_boogie_parse_error(self):
#         verifier = Verifier()
#         assert verifier.analyze('tests/test_specs/parse_error.spec') == False

#     def test_analyze_boogie_type_error(self):
#         verifier = Verifier()
#         assert verifier.analyze('tests/test_specs/type_error.spec') == False

#     def test_analyze_boogie_verification_error(self):
#         verifier = Verifier()
#         assert verifier.analyze('tests/test_specs/verification_error.spec') == False

#     #parsing
#     @patch('soteria.parser.Parser.parse')
#     def test_analyze_parse_called(self, mock):
#         verifier = Verifier()
#         verifier.analyze('tests/test_specs/correct.spec')
#         assert mock.called == True

#     #compliance checks
#     # @patch('soteria.checks.compliance_checker.ComplianceChecker.check')
#     # def test_analyze_compliance_checker_called(self, mock):
#     #     verifier = Verifier()
#     #     verifier.analyze('tests/test_specs/correct.spec')
#     #     assert mock.called == True

#     # def test_analyze_compliance_error(self):
#     #     verifier = Verifier()
#     #     assert verifier.analyze('tests/test_specs/compliance_error.spec') == False

#     #convergence checks
#     @patch('soteria.checks.convergence_checker.ConvergenceChecker.check')
#     def test_analyze_convergence_checker_called(self, mock):
#         verifier = Verifier()
#         verifier.analyze('tests/test_specs/correct.spec')
#         assert mock.called == True

#     #safety checks
#     @patch('soteria.checks.safety_checker.SafetyChecker.check')
#     def test_analyze_safety_checker_called(self, mock):
#         verifier = Verifier()
#         verifier.analyze('tests/test_specs/correct.spec')
#         assert mock.called == True

#     def test_analyze_correct_specification(self):
#         verifier = Verifier()
#         result = verifier.analyze('tests/test_specs/correct.spec')
#         assert result == True