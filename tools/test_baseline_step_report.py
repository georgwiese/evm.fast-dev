"""Check measurement framing and total-reader semantics on adversarial offsets."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("report", Path(__file__).with_name("baseline-step-report.py"))
report = importlib.util.module_from_spec(spec)
spec.loader.exec_module(report)


def pack(blob):
    return len(blob).to_bytes(8, "little") + blob + bytes((-len(blob)) % 8)


class InputFields(unittest.TestCase):
    def test_empty_total_reader(self):
        row = report.input_fields(pack(b""))
        self.assertEqual(row["declared_gas_limit"], 0)
        self.assertIsNone(row["payload_gas_used"])

    def test_noncanonical_offsets_and_exact_cap(self):
        blob = bytearray(1000)
        blob[2:6] = (80).to_bytes(4, "little")
        blob[82:86] = (100).to_bytes(4, "little")
        blob[594:602] = (200_000_000).to_bytes(8, "little")
        blob[602:610] = (123).to_bytes(8, "little")
        row = report.input_fields(pack(blob))
        self.assertEqual(row["declared_gas_limit"], 200_000_000)
        self.assertEqual(row["payload_gas_used"], 123)
        self.assertTrue(row["covered_gas"])
        blob[594:602] = (200_000_001).to_bytes(8, "little")
        self.assertFalse(report.input_fields(pack(blob))["covered_gas"])

    def test_truncated_word_zero_extends(self):
        blob = bytearray(416)
        blob[414:416] = b"\x34\x12"
        self.assertEqual(report.input_fields(pack(blob))["declared_gas_limit"], 0x1234)

    def test_outside_offset_reads_zero(self):
        self.assertEqual(report.input_fields(pack(b"\x15\x01" + b"\xff" * 4))
                         ["declared_gas_limit"], 0)

    def test_bad_transport_rejected(self):
        for packed in [b"", (10).to_bytes(8, "little"), pack(b"x")[:-1],
                       pack(b"x")[:-1] + b"\x01"]:
            with self.assertRaises(ValueError):
                report.input_fields(packed)

    def test_missing_counts_and_zero_gas_excluded_from_ratio(self):
        rows = [dict(label="zero", **{"class": "PASS(full)"}, spike_instructions=3,
                     payload_gas_used=0, covered_gas=True),
                dict(label="missing", **{"class": "PASS(full)"}, spike_instructions=None,
                     payload_gas_used=2, covered_gas=True)]
        result = report.summary(rows)
        self.assertEqual(result["mean"], 3)
        self.assertIsNone(result["highest_instructions_per_payload_gas"])


if __name__ == "__main__":
    unittest.main()
