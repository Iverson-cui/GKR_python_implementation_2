#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Jul 18 21:49:06 2022

@author: raju
"""


import numpy as np

# import math
# import random


import sumcheck_util as SU
import circuit
import time
from interactor_GKR import Interactor

DEBUG_INFO = True
TIME_INFO = False


class Verifier(Interactor):
    """
    Verifier is a subclass of interactor.
    The only extra internal variable is: claimed_values_at_end_of_layer. This is a list,
    whose i^th entry is the value that the prover implicit claims is \tilde{W}_i(random_vector[i])
    through the protocol (i.e., it is the evaluation of a univariate polynomial at
    a random number that the verifier chooses.)
    """

    def __init__(self, C: circuit):
        Interactor.__init__(self, C)
        self.claimed_values_at_end_of_layer = []

    def get_claimed_values_at_end_of_layer(self):
        return self.claimed_values_at_end_of_layer

    def get_claimed_value_at_end_of_layer(self, i):
        assert (
            i >= 0 and i < 2 * self.get_depth()
        ), "the layer i must be between {} and {}".format(1, 2 * self.get_depth())
        return self.claimed_values_at_end_of_layer[i]

    def append_claimed_values_at_end_of_layer(self, val):
        self.claimed_values_at_end_of_layer.append(val)

    def output_layer_communication(self, D):
        """
        After accepting D, the prover output layer dictionary, it returns a random vector. Verifier also computes the MLE of dictionary evaluated at the random vector. When starting the GKR, we first have to have a output MLE value, then based on that value we execute sumcheck on the f function.
        """
        k = self.circ.get_k()  # k is a list of the log (base 2) of number of gates
        # in each layer.
        p = self.p
        first_random_vector = tuple([np.random.randint(0, p) for i in range(k[0])])
        self.random_vectors.append(first_random_vector)
        value_at_first_random_vector = SU.eval_MLE(D, first_random_vector, k[0], p)
        self.append_evaluations_RV(value_at_first_random_vector)
        return first_random_vector

    def partial_sumcheck_check(self, i: int, s: int, poly: list):
        """
        partial_sumcheck_check
        INPUTS: i (integer), s (integer), poly (list)
        OUTPUTS: new_random_element

        This is the verifier's side of the sumcheck protocol. Here, i is the layer,
        s is the step in the sumcheck within the layer, and poly is the last thing that
        the prover sent to us. (For the initial message, which is simply a number, we
        had the prover send it over as [val, 0, 0], i.e., the constant quadratic polynomial)

        if the checks are satisfied, we have the verifier send fresh randomness.
        """
        p = self.p
        d = self.d
        copy_k = self.get_circ().get_copy_k()
        k = self.get_k()
        num_copy = self.get_num_copy()
        assert i >= 0 and i < d, "i is out of bounds"
        assert (
            s >= 0 and s <= k[i + 1] - num_copy[i]
        ), "step must be between 0 and k[i+1]-num_copy[i]"
        # we will separate out three cases: s = 0, s = 1, and all other cases.
        if s == 0:
            # poly represents the *value* that the prover is claiming. I.e.,
            # Prover claims \tilde{W}_i(last_random_vector) = val (in the form of
            # [val, 0, 0]). He will spend the rest of the sumcheck locally verifying this
            # and eventually reducing it to a claim about \tilde{W}_{i+1}
            if i >= 2:
                assert poly[0] == self.get_claimed_value_at_end_of_layer(
                    i - 1
                ), "The claimed value at the end of step {}, {} does not match with what the prover just sent, {}".format(
                    i - 1, self.get_claimed_value_at_end_of_layer(i - 1), poly[0]
                )
            self.append_sumcheck_polynomial(i, poly)
            # if s == 0, don't return anything
            return 0
        elif s == 1:
            # first, check compatibility of the 0th and first poly.
            sum_new_poly_at_0_1 = (
                SU.quadratic_evaluation(poly, 0, p)
                + SU.quadratic_evaluation(poly, 1, p)
            ) % p
            old_value = SU.quadratic_evaluation(
                self.get_specific_polynomial(i, s - 1), 0, p
            )
            assert (
                sum_new_poly_at_0_1 == old_value % p
            ), "the first check failed, {} is not equal to {}".format(
                sum_new_poly_at_0_1, old_value
            )
            #            print("layer {} step 1 succeeded!".format(i))
            # Now the verification passes, verifier generate random challenges.
            self.append_sumcheck_polynomial(i, poly)
            new_random_element = np.random.randint(0, p)
            self.append_element_SRE(i, new_random_element)
            return new_random_element
        elif 1 < s <= k[i + 1] - num_copy[i]:
            # The reason to separate out the case s == 1 is that, in each round of sumcheck we need to compare MLE at 0 + MLE at 1 = last round value. Last round value is calculated when used. This means we have to obtain the random element and poly of last round every time. When s=1, there is no last round random element, and poly is just a value.
            r = self.get_sumcheck_random_element(i, s - 1)
            sum_new_poly_at_0_1 = (
                SU.quadratic_evaluation(poly, 0, p)
                + SU.quadratic_evaluation(poly, 1, p)
            ) % p
            old_value = SU.quadratic_evaluation(
                self.get_specific_polynomial(i, s - 1), r, p
            )
            assert (
                sum_new_poly_at_0_1 == old_value % p
            ), "the check failed at layer {} step {}, {} is not equal to {}. copy_k[i]={},copy_k[i+1]={}".format(
                i, s, sum_new_poly_at_0_1, old_value, copy_k[i], copy_k[i + 1]
            )
            #            print("layer {} step {} succeeded!".format(i, s))
            # Now the verification passes, verifier generate random challenges.

            # first, append the polynomial that has passed the verification to the list of polynomials.
            self.append_sumcheck_polynomial(i, poly)
            new_random_element = np.random.randint(0, p)
            # Then append the random challenge of the last variable to the SRE list.
            self.append_element_SRE(i, new_random_element)

            if s == k[i + 1] - num_copy[i]:
                layer_i_random_elements = self.get_layer_i_sumcheck_random_elements(i)
                assert (
                    len(layer_i_random_elements) == k[i + 1] - num_copy[i]
                ), "the number of random elements the verifier has added to layer {} is not 2*k[i+1], which means {} is not {}".format(
                    i, len(layer_i_random_elements), 2 * copy_k[i + 1]
                )

            return new_random_element

    def partial_sumcheck_check_mult_layer(self, layer: int, step: int, poly: int):
        """
        This function is used to specifically check the last layer of the circuit.
        """
        p = self.p
        d = self.d
        k = self.get_k()
        num_copy = self.get_num_copy()
        copy_k = self.get_circ().get_copy_k()
        assert (
            0 <= step <= k[layer] + 2 * (k[layer + 1] - num_copy[layer])
        ), "step must be between 0 and 2*copy_k_{i+1}"

        if step == 0:
            assert poly[0] == self.get_claimed_value_at_end_of_layer(
                layer - 1
            ), "The claimed value at the end of step {}, {} does not match with what the prover just sent, {}".format(
                layer - 1, self.get_claimed_value_at_end_of_layer(layer - 1), poly[0]
            )
            self.append_sumcheck_polynomial(layer, poly)
            # if s == 0, don't return anything
            return 0
        if step == 1:
            assert (
                len(poly) == 4
            ), "the poly at layer {} step {} should be of length 4, but got {}".format(
                layer, step, len(poly)
            )
            sum_new_poly_at_0_1 = (
                SU.cubic_evaluation(poly, 0, p) + SU.cubic_evaluation(poly, 1, p)
            ) % p
            old_value = SU.quadratic_evaluation(
                self.get_specific_polynomial(layer, step - 1), 0, p
            )
            assert (
                sum_new_poly_at_0_1 == old_value % p
            ), "the first check failed, {} is not equal to {}".format(
                sum_new_poly_at_0_1, old_value
            )
            #            print("layer {} step 1 succeeded!".format(i))
            # Now the verification passes, verifier generate random challenges.
            self.append_sumcheck_polynomial(layer, poly)
            new_random_element = np.random.randint(0, p)
            self.append_element_SRE(layer, new_random_element)
            return new_random_element
        if 1 < step <= k[layer] + 2 * (k[layer + 1] - num_copy[layer]):
            r = self.get_sumcheck_random_element(layer, step - 1)
            assert (
                len(poly) == 4
            ), "the poly at layer {} step {} should be of length 4, but got {}".format(
                layer, step, len(poly)
            )
            sum_new_poly_at_0_1 = (
                SU.cubic_evaluation(poly, 0, p) + SU.cubic_evaluation(poly, 1, p)
            ) % p
            old_value = SU.cubic_evaluation(
                self.get_specific_polynomial(layer, step - 1), r, p
            )
            assert (
                sum_new_poly_at_0_1 == old_value % p
            ), "the check failed at layer {} step {}, {} is not equal to {}. copy_k[layer]={},copy_k[layer+1]={}".format(
                layer,
                step,
                sum_new_poly_at_0_1,
                old_value,
                copy_k[layer],
                copy_k[layer + 1],
            )
            self.append_sumcheck_polynomial(layer, poly)
            new_random_element = np.random.randint(0, p)
            self.append_element_SRE(layer, new_random_element)
            return new_random_element
        assert False, "step must be between 0 and {}".format(
            k[layer] + 2 * (k[layer + 1] - num_copy[layer])
        )

    def reduce_two_to_one(self, i: int, poly: list):
        """
        reduce_two_to_one
        INPUTS: i (integer), poly (list)
        OUTPUTS: new_random_vector (tuple)
        At the end of the sumcheck protocol for layer i, we have just received a
        polynomial, poly, that the prover claims to be \tilde{W}_{i+1} restricted to the line
        between bstar and cstar. More precisely:
            poly(0) is claimed to be \tilde{W}_{i+1}(bstar) and
            poly(1) is claimed to be \tilde{W}_{i+1}(cstar)
        We may use this to construct a "current" claim about what f^i_{RV_i} is at
        (bstar, cstar). There is a second, "old" claimed value: the last quadratic
        polynomial sent, evaluated at the last random element the verifier picked.
        If this passes, then the verifier picks a random element e in F_p, gets
        a new_random_vector via the line function, and binds the Prover to poly(e).
        We have therefore reduced ourselves to a statement about \tilde{W}_{i+1}.
        """
        # phase 1: verification
        num_copy = self.get_num_copy()
        p = self.get_p()
        k = self.get_k()
        circ = self.get_circ()
        copy_k = circ.get_copy_k()
        z_tuple = self.get_random_vector(i)
        # The verifier needs to get the poly evaluated at 0 and 1 cause they are the claimed value of the prover
        if TIME_INFO:
            poly_start_time = time.time()
        vals = [SU.polynomial_evaluation(poly, i, p) for i in range(2)]
        if TIME_INFO:
            poly_end_time = time.time()
            print(
                "Time for layer {} poly evaluation: {}".format(
                    i, poly_end_time - poly_start_time
                )
            )
        a1_last_layer = self.get_layer_i_sumcheck_random_elements(i)[0]
        a2_last_layer = self.get_layer_i_sumcheck_random_elements(i)[-num_copy[i] :]
        if not i == self.get_depth() - 1:
            self.process_SRE_for_parallelism(i, z_tuple[: self.get_num_copy()[i + 1]])
        else:
            self.process_SRE_for_parallelism(i, tuple(a2_last_layer))
        SRE_layer_i = self.get_layer_i_sumcheck_random_elements(i)
        self.append_line(self.compute_line(i))
        # bstar and cstar is the input of W_i function for verification.
        bstar = tuple(SRE_layer_i[: k[i + 1]])
        cstar = tuple(SRE_layer_i[k[i + 1] :])
        RV_i = tuple(z_tuple)
        last_poly = self.get_specific_polynomial(i, -1)
        # To verify the claim, the verifier needs to know the values of add and mult.
        if TIME_INFO:
            add_mult_start_time = time.time()
        # Although random vector and random element are of length k[i] and 2*k[i+1] respectively, we only need to evaluate add and mult at their gate label.
        add_bstar_cstar = circ.eval_MLE_add(
            i, RV_i[-copy_k[i] :] + bstar[-copy_k[i + 1] :] + cstar[-copy_k[i + 1] :]
        )
        mult_bstar_cstar = circ.eval_MLE_mult(
            i, (a1_last_layer,) + bstar[num_copy[i] :] + cstar[num_copy[i] :]
        )
        if TIME_INFO:
            add_mult_end_time = time.time()
            print(
                "Time for layer {} add and mult evaluation: {}".format(
                    i, add_mult_end_time - add_mult_start_time
                )
            )
        # compute what the prover claims f_i(SRE_layer_i) is based on
        # what the prover claims W_{i+1}(bstar) and W_{i+1}(cstar) are.
        # (this is via the polynomial that the prover sends!!)
        if not i == self.circ.get_depth() - 1:
            current_claimed_value_of_fi = (add_bstar_cstar * (vals[0] + vals[1])) % p
        else:
            current_claimed_value_of_fi = (
                SU.chi(RV_i, tuple(a2_last_layer) + (a1_last_layer,), k[i], p)
                * (mult_bstar_cstar * (vals[0] * vals[1]))
                % p
            )
        # The verifier needs to get the old claimed value to compare it with the new one.
        if TIME_INFO:
            old_claimed_value_start_time = time.time()
        if i == self.get_circ().get_depth() - 1:
            old_claimed_value_of_fi = SU.cubic_evaluation(
                last_poly, a2_last_layer[-1], p
            )
        else:
            old_claimed_value_of_fi = SU.quadratic_evaluation(
                last_poly, SRE_layer_i[-1], p
            )
        if TIME_INFO:
            old_claimed_value_end_time = time.time()
            print(
                "Time for layer {} old claimed value evaluation: {}".format(
                    i, old_claimed_value_end_time - old_claimed_value_start_time
                )
            )
        assert (
            current_claimed_value_of_fi == old_claimed_value_of_fi
        ), "The first check at the end of sumcheck for layer {} failed: there is an imcompatibility between the last polynomial and the claimed values of \tilde W_i+1(bstar) and \tilde W_i+1(cstar) {}!={}".format(
            i, current_claimed_value_of_fi, old_claimed_value_of_fi
        )
        if DEBUG_INFO:
            print(
                "The two claimed values of f^{} (with random vector {}) at {} agree: {} and {}".format(
                    i,
                    self.get_random_vector(i),
                    SRE_layer_i,
                    old_claimed_value_of_fi,
                    current_claimed_value_of_fi,
                )
            )

        # Phase 2: get the next layer claim
        line = self.get_line(i)
        final_random_element_in_layer = np.random.randint(0, p)
        new_random_vector = line(final_random_element_in_layer)
        self.append_RV(new_random_vector)
        self.append_claimed_values_at_end_of_layer(
            SU.polynomial_evaluation(poly, final_random_element_in_layer, p)
        )

        return new_random_vector

    def encapsulate_verification_check(self, random_vector: list, value: int):
        """
        In encapsulation version, there is no line. We just need to check the unique claim.
        """
        self.append_RV(tuple(random_vector))
        self.append_claimed_values_at_end_of_layer(
            # SU.DP_eval_MLE(
            #     self.circ.get_W(num_layer + 1),
            #     random_vector,
            #     self.get_k()[num_layer + 1],
            #     self.get_p(),
            # )
            value
        )
        self.append_line(random_vector)
        return random_vector

    def reduce_two_to_one_without_verification(self, i: int, poly: list):
        """
        BEFORE:
        With the help of time test we know that verifier.reduce_two_to_one is the most time consuming part of the GKR protocol.
        We try to dig out why. This function I remove the verification part of reduce_two_to_one. To see if the time is reduced.
        If you want to use it in the command_GKR.py, you have to change where reduce_two_to_one to this function, and other parts of the code goes as usual.
        AFTER:
        Now we know it's just a bug causing empty loop to drag time. When the bug is fixed, there is no need to call this function.
        """
        p = self.get_p()
        k = self.get_k()
        circ = self.get_circ()
        copy_k = circ.get_copy_k()
        z_tuple = self.get_random_vector(i)
        # The verifier needs to get the poly evaluated at 0 and 1 cause they are the claimed value of the prover
        # if TIME_INFO:
        #     poly_start_time = time.time()
        # vals = [SU.polynomial_evaluation(poly, i, p) for i in range(2)]
        # if TIME_INFO:
        #     poly_end_time = time.time()
        #     print(
        #         "Time for layer {} poly evaluation: {}".format(
        #             i, poly_end_time - poly_start_time
        #         )
        #     )
        # SRE_layer_i = self.get_layer_i_sumcheck_random_elements(i)
        self.process_SRE_for_parallelism(i, z_tuple[: k[i + 1] - copy_k[i + 1]])
        self.append_line(self.compute_line(i))
        p = self.get_p()
        line = self.get_line(i)
        final_random_element_in_layer = np.random.randint(0, p)
        new_random_vector = line(final_random_element_in_layer)
        self.append_RV(new_random_vector)
        self.append_claimed_values_at_end_of_layer(
            SU.polynomial_evaluation(poly, final_random_element_in_layer, p)
        )

        return new_random_vector

    def final_verifier_check(self):
        """
        final_verifier_check
        OUTPUTS: True if we get to the end
        Here, we compare the two claimed values of \tilde{W}_d(RV[d])
        """
        d = self.get_depth()
        circ = self.get_circ()
        p = self.get_p()
        k = self.get_k()
        Wd = circ.get_W(d)
        RV_d = tuple(self.get_random_vector(d))
        last_claimed_value = self.get_claimed_value_at_end_of_layer(d - 1)
        # We can now evaluate the MLE at the random vector since we know the input value.
        actual_value_at_RV = SU.eval_MLE(Wd, RV_d, k[d], p)
        assert last_claimed_value == actual_value_at_RV, "{} is not equal to {}".format(
            last_claimed_value, actual_value_at_RV
        )
        return True
