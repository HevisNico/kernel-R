"""The Python kernel against the properties that the Lean file of the qualification proves."""
import random
import unittest

import kernel as K


def random_bounds(rng):
    S, H, eps = rng.randint(0, 50), rng.randint(0, 40), rng.randint(0, 10)
    Dmin = H + rng.randint(0, 60)
    Dmax = Dmin + rng.randint(0, 10)
    room = rng.randint(0, 30)
    C = S + 2 * H + 2 * eps + Dmax + room
    return K.Bounds(S=S, H=H, Dmin=Dmin, Dmax=Dmax, linear_capacity=C + rng.randint(0, 5), semantic_capacity=C, epsilon=eps)


class KernelTests(unittest.TestCase):
    def test_capacity_is_the_smaller_one(self):
        b = K.Bounds(0, 1, 2, 3, 100, 40, 1)
        self.assertEqual(b.capacity, 40)
        self.assertEqual(K.Bounds(0, 1, 2, 3, 30, 40, 1).capacity, 30)

    def test_room_condition(self):
        b = K.Bounds(S=5, H=3, Dmin=10, Dmax=12, linear_capacity=10**6, semantic_capacity=5 + 6 + 4 + 12, epsilon=2)
        self.assertTrue(b.well_formed() and b.room() == 0)
        self.assertFalse(K.Bounds(5, 3, 10, 12, 10**6, 26, 2).well_formed())
        self.assertFalse(K.Bounds(5, 11, 10, 12, 10**6, 10**6, 2).well_formed())       # Dmin below H

    def test_choose_is_the_lean_definition(self):
        b = K.Bounds(S=10, H=4, Dmin=20, Dmax=22, linear_capacity=100, semantic_capacity=60, epsilon=2)
        self.assertEqual(K.choose(b, 14, 38), K.MAINTENANCE)       # 38 + 22 <= 60
        self.assertEqual(K.choose(b, 20, 39), K.WAIT)              # no headroom, 10 + 8 <= 20
        self.assertEqual(K.choose(b, 17, 39), K.REFUSE)            # no headroom, lower under S + 2H
        self.assertEqual(K.choose(b, 13, 20), K.REFUSE)            # not ready
        self.assertEqual(K.choose(b, 30, 20), K.REFUSE)            # empty interval

    def test_every_enclosed_run_is_safe_and_never_refuses(self):
        rng = random.Random(20261113)
        for _ in range(400):
            b = random_bounds(rng)
            self.assertTrue(b.well_formed())
            if b.S + b.H + 2 * b.epsilon > b.capacity - 2 * b.epsilon:
                continue                                  # no reserve at which every sound report is an entry certificate
            reserve = rng.randint(b.S + b.H + 2 * b.epsilon, b.capacity - 2 * b.epsilon)
            carry = K.entry(b, reserve + rng.randint(-b.epsilon, b.epsilon))
            self.assertIsNotNone(carry)
            for _ in range(200):
                self.assertTrue(b.S + b.H <= carry <= reserve <= b.capacity)                 # the invariant
                report = reserve + rng.randint(-b.epsilon, b.epsilon)
                action, lo, hi, nxt = K.step(b, carry, report)
                self.assertNotEqual(action, K.REFUSE)
                self.assertTrue(lo <= reserve <= hi)
                loss = rng.randint(0, b.H)
                self.assertGreaterEqual(reserve - loss, b.S)                                 # the service floor
                if action == K.MAINTENANCE:
                    self.assertLessEqual(hi + b.Dmax, b.capacity)                            # the mandatory guard
                    reserve = reserve - loss + rng.randint(b.Dmin, b.Dmax)
                else:
                    reserve -= loss
                carry = nxt

    def test_preparation_keeps_its_headroom_and_entry_needs_both_ends(self):
        b = K.Bounds(S=10, H=4, Dmin=20, Dmax=22, linear_capacity=100, semantic_capacity=60, epsilon=2)
        self.assertEqual(K.prepare(b, 36), K.MAINTENANCE)
        self.assertEqual(K.prepare(b, 37), K.WAIT)
        self.assertIsNone(K.entry(b, 15))            # lower bound 13 under S + H
        self.assertEqual(K.entry(b, 16), 14)
        self.assertIsNone(K.entry(b, 59))            # upper bound over the capacity

    def test_loss_beyond_the_bound_ends_in_a_refusal_not_in_a_silent_wait(self):
        b = K.Bounds(S=10, H=4, Dmin=20, Dmax=22, linear_capacity=100, semantic_capacity=60, epsilon=2)
        reserve, carry, seen = 40, K.entry(b, 40), []
        for _ in range(30):
            action, lo, hi, carry = K.step(b, carry, reserve)
            seen.append(action)
            if action == K.REFUSE:
                break
            reserve += -30 + (21 if action == K.MAINTENANCE else 0)      # a loss far above H
        self.assertEqual(seen[-1], K.REFUSE)


if __name__ == "__main__":
    unittest.main()
