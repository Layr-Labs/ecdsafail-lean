"""Boundary checks for the empirical mathematical evaluator, not gate proofs."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('sample_b5', Path(__file__).parents[1]/'scripts/sample_b5.py')
b = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)

class SamplingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.table = b.scalar_table()

    def test_group_and_exception(self):
        self.assertIsNone(b.multiply(b.N, self.table))
        self.assertEqual(b.multiply(b.N-1, self.table), (b.G[0], -b.G[1] % b.P))
        fourth = b.multiply(b.N-2, self.table)
        # Must be disabled before evaluating any trajectory or zero inverse.
        self.assertEqual(b.classify(fourth, b.G, [], [], 6, 5), [False]*9)

    def test_uniform_sampler_point_math(self):
        for k in (2, 3, 17, 65537):
            x, y = b.multiply(k, self.table)
            self.assertEqual((y*y-x*x*x-7) % b.P, 0)
        self.assertEqual(b.multiply(2, self.table), b.add(b.G, b.G))

    def test_window_and_fold_boundaries(self):
        self.assertTrue(b.fits(-32, 5)); self.assertFalse(b.fits(32, 5))
        self.assertFalse(b.no_borrow(1))
        self.assertTrue(b.no_borrow(b.C))
        for r in (0, 1, b.C, b.P-1, b.P):
            self.assertEqual(2*b.halve(r) % b.P, r % b.P)

    def test_step_and_freeze(self):
        self.assertEqual(b.step((0, 11, 3, 0, 1)), (0, 3, -4, 2, 1))
        windows = [(600,600,600,600)]*533
        flags, rows, rider = b.trajectory(0, windows, [600]*533, 12, 5)
        self.assertTrue(flags[2])  # conservative early-zero failure
        self.assertEqual(rows[2], 0)
        self.assertEqual(rider, 1)  # armed post-step detection, not premature freeze

    def test_fused_boundary_failures(self):
        self.assertEqual(b.fused(0,0,False), [False]*4)
        self.assertTrue(b.fused(-(2**58),0,False)[1])
        self.assertTrue(b.fused(2**280,0,False)[1])

if __name__ == '__main__': unittest.main()
