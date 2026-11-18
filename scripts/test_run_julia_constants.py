"""Regression tests for rejecting a zero-exit Julia process with failed checks."""
import unittest

from run_julia_constants import VerificationFailure, validate_output


class ConstantRunnerTests(unittest.TestCase):
    def test_successful_checks(self):
        self.assertEqual(validate_output(0, "constant a  1   OK\nconstant b  2   OK\n"), 2)

    def test_printed_failure_with_zero_exit_is_rejected(self):
        with self.assertRaises(VerificationFailure):
            validate_output(0, "constant a  1   OK\nconstant b  2   FAIL\n")

    def test_nonzero_exit_is_rejected(self):
        with self.assertRaises(VerificationFailure):
            validate_output(1, "constant a  1   OK\n")

    def test_empty_run_is_rejected(self):
        with self.assertRaises(VerificationFailure):
            validate_output(0, "")

    def test_header_without_checks_is_rejected(self):
        with self.assertRaises(VerificationFailure):
            validate_output(0, "== Constant checks ==\n")


if __name__ == "__main__":
    unittest.main()
