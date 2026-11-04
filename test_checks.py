#!/usr/bin/env python3
"""Mutation tests for the published checks: each one must fail when its input is broken.

partition.py      the stored netlist passes; the same netlist with one row removed from a shared LUT's table fails.
larger_decoders   each built network passes; a network with two outputs swapped, a LUT given a seventh input, a
                  third level, or a missing output fails.

    python3 -O -m unittest test_checks.py
"""
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import larger_decoders  # noqa: E402


def run_partition(blif_text):
    path = os.path.join(tempfile.mkdtemp(prefix='check_test_'), 'out.blif')
    with open(path, 'w', newline='\n') as handle:
        handle.write(blif_text)
    run = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'partition.py'), path], capture_output=True,
                         text=True)
    return run.returncode, run.stdout


class Partition(unittest.TestCase):
    def setUp(self):
        with open(os.path.join(HERE, 'record', 'out.blif')) as handle:
            self.blif = handle.read()

    def test_the_stored_netlist_passes(self):
        code, out = run_partition(self.blif)
        self.assertEqual(code, 0, out)
        self.assertIn('holds', out)

    def test_a_changed_shared_table_fails(self):
        lines = self.blif.splitlines()
        start = next(i for i, l in enumerate(lines) if l.startswith('.names') and l.endswith('dec_y0'))
        del lines[start + 1]  # drop the first on-set row of Y0
        code, out = run_partition('\n'.join(lines) + '\n')
        self.assertEqual(code, 1, out)
        self.assertIn('FAILS', out)


DEC_AIG = os.environ.get('DEC_AIG', os.path.join(HERE, 'dec.aig'))


def run_simulation(blif_text):
    if not os.path.exists(DEC_AIG):
        raise FileNotFoundError(f'{DEC_AIG} is missing: fetch the benchmark as the README shows, or set DEC_AIG')
    path = os.path.join(tempfile.mkdtemp(prefix='check_test_'), 'out.blif')
    with open(path, 'w', newline='\n') as handle:
        handle.write(blif_text)
    run = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'simulate_dec.py'), DEC_AIG, path],
                         capture_output=True, text=True)
    return run.returncode, run.stdout


class Simulation(unittest.TestCase):
    def setUp(self):
        with open(os.path.join(HERE, 'record', 'out.blif')) as handle:
            self.lines = handle.read().splitlines()

    def names_line(self, output):
        return next(i for i, l in enumerate(self.lines) if l.startswith('.names') and l.split()[-1] == output)

    def test_the_stored_netlist_passes(self):
        code, out = run_simulation('\n'.join(self.lines) + '\n')
        self.assertEqual(code, 0, out)

    def test_two_swapped_outputs_fail(self):
        a, b = self.names_line('selectp1[3]'), self.names_line('selectp1[4]')
        self.lines[a + 1], self.lines[b + 1] = self.lines[b + 1], self.lines[a + 1]
        code, out = run_simulation('\n'.join(self.lines) + '\n')
        self.assertEqual(code, 1, out)
        self.assertIn('2 differ', out)

    def test_a_buffer_fails(self):
        i = self.names_line('dec_y0')
        sig = self.lines[i].split()
        end = next(j for j in range(i + 1, len(self.lines)) if self.lines[j].startswith('.'))
        self.lines[i:end] = ['.names ' + ' '.join(sig[1:]), '1----- 1']  # dec_y0 becomes a buffer of count[0]
        code, out = run_simulation('\n'.join(self.lines) + '\n')
        self.assertEqual(code, 1, out)
        self.assertIn('constant, buffer or inverter', out)

    def test_a_third_level_fails(self):
        i = self.names_line('selectp2[9]')
        self.lines[i] = self.lines[i].replace('selectp2[9]', 'pre9')
        self.lines[i + 2:i + 2] = ['.names pre9 count[0] count[1] count[2] count[3] count[4] selectp2[9]', '1----- 1']
        code, out = run_simulation('\n'.join(self.lines) + '\n')
        self.assertEqual(code, 1, out)


class LargerDecoders(unittest.TestCase):
    def network(self, n):
        blif, sizes = larger_decoders.block_netlist(n)
        return blif, sum(1 << b for b in sizes if b >= 2)

    def test_built_networks_pass(self):
        for n in (9, 10, 11, 12):
            blif, shared = self.network(n)
            self.assertTrue(larger_decoders.accept(blif, n, shared)[0], n)

    def test_two_swapped_outputs_fail(self):
        blif, shared = self.network(9)
        blif = blif.replace(' o5\n', ' TMP\n').replace(' o6\n', ' o5\n').replace(' TMP\n', ' o6\n')
        good, measured = larger_decoders.accept(blif, 9, shared)
        self.assertFalse(good)
        self.assertIn('mismatching outputs 2', measured)

    def test_a_seven_input_lut_fails(self):
        blif, shared = self.network(9)
        lines = blif.splitlines()
        i = next(i for i, l in enumerate(lines) if l.startswith('.names') and l.endswith(' o0'))
        lines[i] = lines[i].replace('.names ', '.names x8 ', 1)
        lines[i + 1] = '-' + lines[i + 1]
        self.assertFalse(larger_decoders.accept('\n'.join(lines) + '\n', 9, shared)[0])

    def test_a_third_level_fails(self):
        blif, shared = self.network(9)
        lines = blif.splitlines()
        i = next(i for i, l in enumerate(lines) if l.startswith('.names') and l.endswith(' o0'))
        lines[i] = lines[i].replace(' o0', ' o0_pre')
        lines[i + 2:i + 2] = ['.names o0_pre o0', '1 1']
        good, measured = larger_decoders.accept('\n'.join(lines) + '\n', 9, shared + 1)
        self.assertFalse(good)
        self.assertIn('levels 3', measured)

    def test_a_missing_output_fails(self):
        blif, shared = self.network(9)
        lines = blif.splitlines()
        i = next(i for i, l in enumerate(lines) if l.startswith('.names') and l.endswith(' o7'))
        del lines[i:i + 2]
        self.assertFalse(larger_decoders.accept('\n'.join(lines) + '\n', 9, shared)[0])


if __name__ == '__main__':
    unittest.main()
