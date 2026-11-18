"""Adversarial tests of the machine-readable axiom-audit validator."""
import json
import unittest

from check_all_axioms import AuditError, PREFIX, SCHEMA, validate_audit


def sample_records():
    return [
        {"kind": "begin", "schema": SCHEMA, "expected_count": 2},
        {"kind": "theorem", "declaration": "YangMills.example",
         "user_name": "YangMills.example", "axioms": ["propext", "Quot.sound"]},
        {"kind": "theorem", "declaration": "_private.YangMills.Test.0.YangMills.helper",
         "user_name": "YangMills.helper", "axioms": []},
        {"kind": "end", "schema": SCHEMA, "checked_count": 2},
    ]


def render(records):
    return "\n".join(PREFIX + json.dumps(record) for record in records) + "\n"


class AuditValidatorTests(unittest.TestCase):
    def test_valid_including_private_theorem(self):
        result = validate_audit(render(sample_records()), 2)
        self.assertEqual(result["theorem_count"], 2)
        self.assertEqual(result["status"], "passed")

    def test_rejects_admitted_proof(self):
        entries = sample_records()
        entries[1]["axioms"] = ["sorryAx"]
        with self.assertRaises(AuditError):
            validate_audit(render(entries), 2)

    def test_rejects_custom_axiom(self):
        entries = sample_records()
        entries[1]["axioms"] = ["YangMills.uniformWilsonBound"]
        with self.assertRaises(AuditError):
            validate_audit(render(entries), 2)

    def test_rejects_truncated_theorem_record(self):
        entries = sample_records()
        del entries[1]
        with self.assertRaises(AuditError):
            validate_audit(render(entries), 2)

    def test_rejects_missing_completion_footer(self):
        with self.assertRaises(AuditError):
            validate_audit(render(sample_records()[:-1]), 2)

    def test_rejects_duplicate_theorem(self):
        entries = sample_records()
        entries[2] = entries[1].copy()
        with self.assertRaises(AuditError):
            validate_audit(render(entries), 2)

    def test_rejects_header_footer_count_mismatch(self):
        entries = sample_records()
        entries[-1]["checked_count"] = 3
        with self.assertRaises(AuditError):
            validate_audit(render(entries), 2)

    def test_rejects_error_even_after_complete_report(self):
        with self.assertRaises(AuditError):
            validate_audit(render(sample_records()) + "file.lean:1:0: error: bad\n", 2)

    def test_rejects_insufficient_library_coverage(self):
        with self.assertRaises(AuditError):
            validate_audit(render(sample_records()), 3)

    def test_rejects_malformed_json(self):
        with self.assertRaises(AuditError):
            validate_audit(PREFIX + '{"kind":', 2)

    def test_rejects_concatenated_audits(self):
        with self.assertRaises(AuditError):
            validate_audit(render(sample_records()) * 2, 2)

    def test_rejects_boolean_count(self):
        entries = sample_records()
        entries[0]["expected_count"] = True
        with self.assertRaises(AuditError):
            validate_audit(render(entries), 2)


if __name__ == "__main__":
    unittest.main()
