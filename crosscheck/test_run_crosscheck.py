#!/usr/bin/env python3
"""Regression tests for the cross-check driver's verdicts, run against the real solver.

A broken circuit must fail the run, and an undecided comparison must not pass as held. The tests solve a real
instance with CaDiCaL, decode the network, break it by swapping two output tables, and check that the driver's
judgement turns from held to violation; they also run a real solve under a short time limit and check that the
timeout is judged incomplete.

    CADICAL=/path/to/cadical python3 -m unittest test_run_crosscheck.py
"""
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import direct_roles
import run_crosscheck

CADICAL = os.environ.get('CADICAL', 'cadical')


def solved_network(K, n, extra):
    work = tempfile.mkdtemp(prefix='crosscheck_test_')
    path = os.path.join(work, 'instance.cnf')
    _, _, meta = direct_roles.build(path, K, n, extra)
    answer, model, _ = run_crosscheck.solve(CADICAL, path, 600)
    assert answer == 'SAT', answer
    return direct_roles.decode(model, meta)


class SwappedOutputs(unittest.TestCase):
    def test_a_correct_network_is_held(self):
        nodes, order = solved_network(4, 4, 0)
        mismatches = direct_roles.simulate(nodes, order, 4, 4)
        self.assertEqual(mismatches, 0)
        self.assertEqual(run_crosscheck.judge('SAT', mismatches, 'SAT'), 'ok')

    def test_swapping_two_outputs_is_a_violation(self):
        nodes, order = solved_network(4, 4, 0)
        nodes[1], nodes[2] = nodes[2], nodes[1]  # outputs 1 and 2 now compute each other's minterm
        mismatches = direct_roles.simulate(nodes, order, 4, 4)
        self.assertEqual(mismatches, 4)
        self.assertEqual(run_crosscheck.judge('SAT', mismatches, 'SAT'), 'violation')
        self.assertEqual(run_crosscheck.relate('SAT', mismatches, 'SAT')[0], 'violation')

    def test_swapping_two_outputs_of_a_shared_lut_network_is_a_violation(self):
        nodes, order = solved_network(4, 5, 1)
        self.assertEqual(direct_roles.simulate(nodes, order, 4, 5), 0)
        nodes[0], nodes[31] = nodes[31], nodes[0]
        mismatches = direct_roles.simulate(nodes, order, 4, 5)
        self.assertGreater(mismatches, 0)
        self.assertEqual(run_crosscheck.relate('SAT', mismatches, 'SAT')[0], 'violation')


    def test_a_cyclic_network_is_a_violation(self):
        nodes, order = solved_network(4, 4, 0)
        n = 4
        fanin0, table0 = nodes[0]
        fanin1, table1 = nodes[1]
        nodes[0] = ([n + 1 + 1] + fanin0[1:], table0)  # output 0 reads output 1
        nodes[1] = ([n + 1 + 0] + fanin1[1:], table1)  # output 1 reads output 0
        mismatches = direct_roles.simulate(nodes, order, 4, n)
        self.assertEqual(mismatches, 'invalid')
        self.assertEqual(run_crosscheck.judge('SAT', mismatches, 'SAT'), 'violation')


class PlantedNetworks(unittest.TestCase):
    """The encoding itself, not only its checker: it must admit a known decoder whatever its pin order, and must
    reject the same network once it no longer computes the decoder."""

    def solve_planted(self, K, n, extra, nodes):
        work = tempfile.mkdtemp(prefix='crosscheck_test_')
        path = os.path.join(work, 'planted.cnf')
        _, _, meta = direct_roles.build(path, K, n, extra, plant=nodes)
        answer, model, _ = run_crosscheck.solve(CADICAL, path, 600)
        return answer, model, meta

    def shuffled(self, nodes, K, seed):
        import random
        rng = random.Random(seed)
        out = []
        for fanin, table in nodes:
            perm = list(range(K))
            rng.shuffle(perm)  # new pin p reads old pin perm[p]
            new_table = 0
            for t in range(1 << K):
                old = sum(((t >> p) & 1) << perm[p] for p in range(K))
                if (table >> old) & 1:
                    new_table |= 1 << t
            out.append(([fanin[perm[p]] for p in range(K)], new_table))
        return out

    def test_a_known_network_with_shuffled_pins_is_admitted(self):
        nodes, order = solved_network(4, 5, 1)
        planted = self.shuffled(nodes, 4, seed=7)
        self.assertEqual(direct_roles.simulate(planted, None, 4, 5), 0)
        answer, model, meta = self.solve_planted(4, 5, 1, planted)
        self.assertEqual(answer, 'SAT')
        again, _ = direct_roles.decode(model, meta)
        self.assertEqual(direct_roles.simulate(again, None, 4, 5), 0)

    def test_a_network_with_two_outputs_swapped_is_rejected(self):
        nodes, order = solved_network(4, 5, 1)
        nodes[3], nodes[17] = nodes[17], nodes[3]
        if direct_roles.simulate(nodes, None, 4, 5) == 'invalid':
            self.skipTest('the swap made the network cyclic; covered by the cyclic test')
        answer, _, _ = self.solve_planted(4, 5, 1, nodes)
        self.assertEqual(answer, 'UNSAT')


class Undecided(unittest.TestCase):
    def test_a_timed_out_comparison_is_incomplete(self):
        work = tempfile.mkdtemp(prefix='crosscheck_test_')
        path = os.path.join(work, 'instance.cnf')
        direct_roles.build(path, 4, 6, 1)  # takes over a minute to refute
        answer, model, _ = run_crosscheck.solve(CADICAL, path, 1.0)
        self.assertEqual(answer, 'TIMEOUT')
        self.assertEqual(run_crosscheck.judge(answer, None, 'UNSAT'), 'incomplete')
        self.assertEqual(run_crosscheck.relate(answer, None, 'UNSAT')[0], 'incomplete')

    def test_a_known_mismatch_is_a_violation_even_when_the_reduced_solve_times_out(self):
        nodes, order = solved_network(4, 4, 0)
        nodes[1], nodes[2] = nodes[2], nodes[1]
        mismatches = direct_roles.simulate(nodes, order, 4, 4)
        self.assertEqual(mismatches, 4)
        work = tempfile.mkdtemp(prefix='crosscheck_test_')
        path = os.path.join(work, 'reduced.cnf')
        direct_roles.build(path, 4, 6, 1)  # a real instance that takes over a minute
        reduced, _, _ = run_crosscheck.solve(CADICAL, path, 1.0)
        self.assertEqual(reduced, 'TIMEOUT')
        verdict, relation = run_crosscheck.relate('SAT', mismatches, reduced)
        self.assertEqual(verdict, 'violation')
        self.assertIn('not a decoder', relation)
        self.assertIn('undecided', relation)

    def test_a_contrary_answer_is_a_violation(self):
        self.assertEqual(run_crosscheck.judge('UNSAT', None, 'SAT'), 'violation')
        self.assertEqual(run_crosscheck.relate('SAT', 0, 'UNSAT')[0], 'violation')


if __name__ == '__main__':
    unittest.main()
