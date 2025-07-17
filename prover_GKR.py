#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Jul 18 20:58:15 2022

@author: raju
"""


from interactor_GKR import Interactor

import sumcheck_util as SU
import circuit

DEBUG_INFO = False


class Prover(Interactor):
    """
    Prover class is a subclass of the interactor. Given the base interactor, we also
    compute the circuit. There are no extra internal variables.
    """

    def __init__(self, C: circuit):
        Interactor.__init__(self, C)
        # Prover needs to compute the circuit. This is done once initialized.
        self.circ.compute_circuit()
        self.current_beta_array = []

    def output_layer_communication(self):
        """
        return the output layer function, which is the start of the GKR, claim about the output layer.

        We don't consider the possibility of bad prover. So every message prover sends to Verifier is really from the circuit result.
        """
        return self.circ.get_W(0)

    def receive_random_vector(self, i: int, r_i: tuple):
        """
        receive_random_vector
        INPUT: i (int), r_i (tuple)
        receive_random_vector appends the random vector r_i to random_vectors
        and also appends the correct evalution of W_i.
        Here, i is the layer.
        """
        d = self.d
        k = self.k
        p = self.p
        assert i >= 0 and i <= d, "the layer must be between 0 and d-1"
        self.random_vectors.append(r_i)
        D_i = self.circ.get_W(i)
        # evaluate get_W(i) at the random vector r_i
        evaluation_at_random_vector = SU.DP_eval_MLE(D_i, r_i, k[i], p)
        self.append_evaluations_RV(evaluation_at_random_vector)

    def sum_fi(self, i: int, s: int):
        """
        sum_fi
        INPUTS: i (integer meaning the number of layers), s (step), num_copy (binary representation of the number of copies), RV (random vector sent by verifier, which is the math formula is z, {z_1+z_2}. This vector will be used in evaluation of W_i+1. the length of RV is k[i])
        OUTPUTS: a quadratic polynomial, in the form of a list, i.e. [a, b, c],
            which corresponds to a + bx + cx^2

        sum_fi computes the relevant partial boolean hypercube sum that the prover
        must compute at the sth step of the sumcheck protocol on the ith layer. the function returns a quadratic polynomial.

        the sumcheck is done on a function fi, but we do not independently compute fi; rather,
        we use an optimization.
        here, f^{(i)}_{random_vector[i]} is a function on 2 * k[i+1] variables. (there is an
        implicit parameter, random_vector[i]!! without this implicit parameter,
        the function would be of k[i]+ 2 *k[i+1] variables, but we fix the first k[i]
        inputs!!)

        This function returns what the prover needs to send to the verifier in every round of the sumcheck protocol.
        """

        circ = self.get_circ()
        d = circ.get_depth()
        p = circ.get_p()
        k = circ.get_k()
        copy_k = circ.get_copy_k()
        num_copy = circ.get_num_copy()
        assert i >= 0 and i < d, "i is out of bounds"
        assert i < len(self.get_random_vectors()), "haven't reached this layer yet"
        # the partial sumcheck function address the case of s=0.
        assert (
            1 <= s <= 2 * (k[i + 1] - num_copy[i])
        ), "In parallel settings, the step s in sumcheck is out of bounds"
        # check the len and type of RV
        assert isinstance(
            self.get_random_vector(i), tuple
        ), f"RV must be a tuple, but got {type(self.get_random_vector(i))}"
        assert (
            len(self.get_random_vector(i)) == k[i]
        ), f"RV must have {k[i]} elements, but got {len(self.get_random_vector(i))}"
        poly_values = [
            0,
            0,
            0,
        ]  # initialize the values of my poly at the inputs 0, 1, 2
        # when i==d-1, we need four values because the poly is of degree 3. Later we append this extra_value to poly_values array.
        if i == d - 1:
            extra_value = 0
        #        Li = circ.get_layer(i)
        # N = k[i] + 2 * k[i + 1]
        # the following is the main content of the partial boolean hypercube sum
        # the goal is to compute poly_values. We use a fast evaluation trick:
        # involving summing over the gates. (This is explained in 4.6.5, method 2,
        # of Thaler's book as of 09/04/2022.)

        # Depending on which step we are in, all of the s cases can be separated into four part. 1. 1<=s<k[i+1], where b is half binary and c is full binary. 2. s=k[i+1], where b is full FFE and c is full binary. 3. k[i+1]<s<2*k[i+1], where b is full FFE and c is half binary. 4. s=2*k[i+1], where b is full FFE and c is full FFE.
        # the reason we do this is that when input to W_i+1 is in different categories, ways to evaluate it are different.
        current_random_elements = self.get_layer_i_sumcheck_random_elements(i)
        # bc = (r_0, ..., r_{s-2}, {0/1/2}, b_{s},..b_{k[i]}-1) (as in Method
        # 2 in 4.6.5, with appropriate indices changed). So we only take part of current_random_elements, because it's the final random vector, and we haven't gone that far.
        # the point is we only need to sum over such tuples that agree with
        # the last (however many) bits of a!!
        # bc is separated into 3 parts, tuple of random_elements, x and tuple of a. The length of the tuple of random_elements keeps growing as the step goes up. x is assigned to 0, 1 and 2 later. tuple of a contains the binary bits combinations.

        # bc_partial is the first s-1 bits of random elements. It needs to append 0/1/2.
        bc_partial = tuple(current_random_elements[: s - 1])
        # bc = (
        #     tuple(current_random_elements[: s - 1])
        #     + (x,)
        #     + tuple(a[-(2 * (k[i + 1]) - s) :])
        # )
        # b = bc[: k[i + 1]]
        # c = bc[k[i + 1] :]
        # the first k[i] bits of z are settled before the sumcheck.
        # z = tuple(self.get_random_vector(i)) + bc
        # W_iplus1 is a dictionary that takes in k[i+1] bits.
        W_iplus1 = circ.get_W(i + 1)
        # z2 conform to layer i copy assignment, instead of layer i+1 copy assignment.
        z2 = self.get_random_vector(i)[: num_copy[i]]
        # Initialize variables that might be used later
        Cormode_b_0 = None
        Cormode_b_1 = None
        Cormode_b_2 = None
        Cormode_b_3 = None
        Cormode_c = None
        Cormode_c_0 = None
        Cormode_c_1 = None
        Cormode_c_2 = None
        Cormode_c_3 = None

        # First case. Use cormode for b in every s and Cormode for c once for all s.
        if s < k[i + 1] - num_copy[i]:
            # b: Cormode c: all binary, directly retrieve
            # Cormode_b takes in length copy_k[i+1]-s
            Cormode_b_0 = SU.Cormode_eval_W(
                W_iplus1, z2 + bc_partial + (0,), s + num_copy[i], k[i + 1], p
            )
            Cormode_b_1 = SU.Cormode_eval_W(
                W_iplus1, z2 + bc_partial + (1,), s + num_copy[i], k[i + 1], p
            )
            Cormode_b_2 = SU.Cormode_eval_W(
                W_iplus1, z2 + bc_partial + (2,), s + num_copy[i], k[i + 1], p
            )
            Cormode_b_3 = SU.Cormode_eval_W(
                W_iplus1, z2 + bc_partial + (3,), s + num_copy[i], k[i + 1], p
            )
            # Cormode_c can be optimized. when s<copy_k[i+1], Cormode_c is always the same. But Now I have no idea how to optimize it.
            # Cormode_c takes in length copy_k[i+1]
            Cormode_c = SU.Cormode_eval_W(W_iplus1, z2, num_copy[i], k[i + 1], p)
        # Second case. b is calculated by MLE eval, while c is calculated with the same Cormode as above.
        elif s == k[i + 1] - num_copy[i]:
            Cormode_c = SU.Cormode_eval_W(W_iplus1, z2, num_copy[i], k[i + 1], p)
        # Third case, B is still calculated by MLE, C is calculated by Cormode per step.
        elif k[i + 1] - num_copy[i] < s < 2 * (k[i + 1] - num_copy[i]):
            partial_input_to_c_0 = (
                z2 + bc_partial[k[i + 1] - num_copy[i] : s - 1] + (0,)
            )
            partial_input_to_c_1 = (
                z2 + bc_partial[k[i + 1] - num_copy[i] : s - 1] + (1,)
            )
            partial_input_to_c_2 = (
                z2 + bc_partial[k[i + 1] - num_copy[i] : s - 1] + (2,)
            )
            partial_input_to_c_3 = (
                z2 + bc_partial[k[i + 1] - num_copy[i] : s - 1] + (3,)
            )
            Cormode_c_0 = SU.Cormode_eval_W(
                W_iplus1,
                partial_input_to_c_0,
                s - (k[i + 1] - num_copy[i]) + num_copy[i],
                k[i + 1],
                p,
            )
            Cormode_c_1 = SU.Cormode_eval_W(
                W_iplus1,
                partial_input_to_c_1,
                s - (k[i + 1] - num_copy[i]) + num_copy[i],
                k[i + 1],
                p,
            )
            Cormode_c_2 = SU.Cormode_eval_W(
                W_iplus1,
                partial_input_to_c_2,
                s - (k[i + 1] - num_copy[i]) + num_copy[i],
                k[i + 1],
                p,
            )
            Cormode_c_3 = SU.Cormode_eval_W(
                W_iplus1,
                partial_input_to_c_3,
                s - (k[i + 1] - num_copy[i]) + num_copy[i],
                k[i + 1],
                p,
            )
        else:
            pass
        # The Cormode evaluation should be done before going into each specific gate.
        for gate in range(2 ** copy_k[i]):
            # we use the first copy as an example.
            # gate_inputs goes from 0 to 2 * gate, like [0,1] [2,3] [4,5]...
            gate_inputs = circ.get_inputs(i, gate)
            # a is a boolean string in {0,1}^k[i] \times {0,1}^{2*k[i+1]}
            # which consists (or runs over) triples where the second two parts
            # are input gates to the first piece.
            a = (
                SU.int_to_bin(gate, k[i])
                + SU.int_to_bin(gate_inputs[0], k[i + 1])
                + SU.int_to_bin(gate_inputs[1], k[i + 1])
            )
            # a is composed of: num_copy+copy_k[i]+num_copy+copy_k[i+1]+num_copy+copy_k[i+1] bits.
            # a_gate is used to specifically extract out the gate label of the 3 gates.
            # a_gate contains 3 gate labels. The first is conformed to copy assignment in the i-th layer, the latter two is conformed to copy_assignment in the i+1-th layer.
            a_gate = (
                a[num_copy[i] : k[i]]
                + a[k[i] + num_copy[i] : k[i] + k[i + 1]]
                + a[k[i] + k[i + 1] + num_copy[i] :]
            )
            assert len(a_gate) == copy_k[i] + 2 * (k[i + 1] - num_copy[i])
            # x in range 3 is the common case. For mult case, we need to make x in range 4.
            for x in range(4):
                # common case still only has 3.
                if not i == d - 1:
                    if x == 3:
                        continue
                # No matter in which case, we all get poly_values[x] filled
                gate_type = circ.get_type(i, gate)
                if s < k[i + 1] - num_copy[i]:
                    # b: Cormode c: all binary, directly retrieve
                    if x == 0:
                        W_iplus1_at_b = Cormode_b_0[
                            SU.tuple_to_int(
                                a_gate[
                                    copy_k[i] + s : copy_k[i] + k[i + 1] - num_copy[i]
                                ]
                            )
                        ]
                    elif x == 1:
                        W_iplus1_at_b = Cormode_b_1[
                            SU.tuple_to_int(
                                a_gate[
                                    copy_k[i] + s : copy_k[i] + k[i + 1] - num_copy[i]
                                ]
                            )
                        ]
                    elif x == 2:
                        W_iplus1_at_b = Cormode_b_2[
                            SU.tuple_to_int(
                                a_gate[
                                    copy_k[i] + s : copy_k[i] + k[i + 1] - num_copy[i]
                                ]
                            )
                        ]
                    elif x == 3:
                        W_iplus1_at_b = Cormode_b_3[
                            SU.tuple_to_int(
                                a_gate[
                                    copy_k[i] + s : copy_k[i] + k[i + 1] - num_copy[i]
                                ]
                            )
                        ]
                    else:
                        raise ValueError("x must be 0, 1 or 2, but got {}".format(x))

                    W_iplus1_at_c = Cormode_c[
                        SU.tuple_to_int(a_gate[copy_k[i] + k[i + 1] - num_copy[i] :])
                    ]

                elif s == k[i + 1] - num_copy[i]:
                    # b: all FFE c: all binary, directly retrieve
                    if x == 0:
                        W_iplus1_at_b = SU.DP_eval_MLE(
                            W_iplus1, z2 + bc_partial + (0,), k[i + 1], p
                        )
                    elif x == 1:
                        W_iplus1_at_b = SU.DP_eval_MLE(
                            W_iplus1, z2 + bc_partial + (1,), k[i + 1], p
                        )
                    elif x == 2:
                        W_iplus1_at_b = SU.DP_eval_MLE(
                            W_iplus1, z2 + bc_partial + (2,), k[i + 1], p
                        )
                    elif x == 3:
                        W_iplus1_at_b = SU.DP_eval_MLE(
                            W_iplus1, z2 + bc_partial + (3,), k[i + 1], p
                        )
                    else:
                        raise ValueError("x must be 0, 1 or 2, but got {}".format(x))

                    W_iplus1_at_c = Cormode_c[
                        SU.tuple_to_int(a_gate[copy_k[i] + k[i + 1] - num_copy[i] :])
                    ]

                elif k[i + 1] - num_copy[i] < s < 2 * (k[i + 1] - num_copy[i]):
                    # b: all FFE c: Cormode, directly retrieve
                    W_iplus1_at_b = SU.DP_eval_MLE(
                        W_iplus1, z2 + bc_partial[: k[i + 1] - num_copy[i]], k[i + 1], p
                    )

                    if x == 0:
                        W_iplus1_at_c = Cormode_c_0[
                            SU.tuple_to_int(a_gate[copy_k[i] + s :])
                        ]
                    elif x == 1:
                        W_iplus1_at_c = Cormode_c_1[
                            SU.tuple_to_int(a_gate[copy_k[i] + s :])
                        ]
                    elif x == 2:
                        W_iplus1_at_c = Cormode_c_2[
                            SU.tuple_to_int(a_gate[copy_k[i] + s :])
                        ]
                    elif x == 3:
                        W_iplus1_at_c = Cormode_c_3[
                            SU.tuple_to_int(a_gate[copy_k[i] + s :])
                        ]
                    else:
                        raise ValueError("x must be 0, 1 or 2, but got {}".format(x))

                elif s == 2 * (k[i + 1] - num_copy[i]):
                    W_iplus1_at_b = SU.DP_eval_MLE(
                        W_iplus1, z2 + bc_partial[: k[i + 1] - num_copy[i]], k[i + 1], p
                    )

                    if x == 0:
                        W_iplus1_at_c = SU.DP_eval_MLE(
                            W_iplus1,
                            z2 + bc_partial[k[i + 1] - num_copy[i] :] + (0,),
                            k[i + 1],
                            p,
                        )
                    elif x == 1:
                        W_iplus1_at_c = SU.DP_eval_MLE(
                            W_iplus1,
                            z2 + bc_partial[k[i + 1] - num_copy[i] :] + (1,),
                            k[i + 1],
                            p,
                        )
                    elif x == 2:
                        W_iplus1_at_c = SU.DP_eval_MLE(
                            W_iplus1,
                            z2 + bc_partial[k[i + 1] - num_copy[i] :] + (2,),
                            k[i + 1],
                            p,
                        )
                    elif x == 3:
                        W_iplus1_at_c = SU.DP_eval_MLE(
                            W_iplus1,
                            z2 + bc_partial[k[i + 1] - num_copy[i] :] + (3,),
                            k[i + 1],
                            p,
                        )
                    else:
                        raise ValueError("x must be 0, 1 or 2, but got {}".format(x))
                else:
                    W_iplus1_at_b = 0
                    W_iplus1_at_c = 0
                    raise ValueError(
                        "s must be between 1 and 2*copy_k[i+1], but got {}".format(s)
                    )

                if gate_type == "add":
                    poly_values[x] = (
                        poly_values[x]
                        + SU.chi(
                            a_gate[: copy_k[i] + s],
                            self.get_random_vector(i)[num_copy[i] :]
                            + bc_partial
                            + (x,),
                            copy_k[i] + s,
                            p,
                        )
                        * (W_iplus1_at_b + W_iplus1_at_c)
                    ) % p
                # here we hard-codely assume that mult gates are only contained in the last layer.
                elif gate_type == "mult":
                    if x == 3:
                        extra_value = (
                            extra_value
                            + SU.chi(
                                a_gate[: copy_k[i] + s],
                                self.get_random_vector(i)[num_copy[i] :]
                                + bc_partial
                                + (x,),
                                copy_k[i] + s,
                                p,
                            )
                            * (W_iplus1_at_b * W_iplus1_at_c)
                        ) % p
                    else:
                        poly_values[x] = (
                            poly_values[x]
                            + SU.chi(
                                a_gate[: copy_k[i] + s],
                                self.get_random_vector(i)[num_copy[i] :]
                                + bc_partial
                                + (x,),
                                copy_k[i] + s,
                                p,
                            )
                            * (W_iplus1_at_b * W_iplus1_at_c)
                        ) % p
        # for degree 2 poly, namely common layers
        if not i == d - 1:
            poly = SU.quadratic_interpolate(poly_values, p)
            return poly
        # for degree 3 poly, namely the last layer
        else:
            poly_values.append(extra_value)
            poly = SU.cubic_interpolate(poly_values, p)
            return poly

    def reusing_work_beta_initialize(self, layer: int, random_vector: tuple):
        """
        This function initializes the beta array in the mult layer. For initialization, one input tuple is finite field elements while the other is composed of binary elements.
        the array is of length 2^k[i].
        """
        k = self.get_k()
        copy_k = self.get_copy_k()
        assert (
            len(random_vector) == k[layer]
        ), f"random_vector must have {k[layer]} elements, but got {len(random_vector)}"
        # beta is calculated with the sequence of a_1, a_2, gate first, copy second.
        self.current_beta_array = SU.reusing_work_chi(
            (random_vector[-copy_k[layer] :] + random_vector[: -copy_k[layer]]),
            k[layer],
            self.get_p(),
        )
        assert (
            len(self.current_beta_array) == 2 ** k[layer]
        ), f"current_beta_array must have {2**k[layer]} elements, but got {len(self.current_beta_array)}"
        return self.current_beta_array

    def reusing_work_beta_update(self, z_j: int, random_challenge: int):
        """
        This function updates the beta array given this step random challenge.
        """
        # depth = self.get_depth()
        # k = self.get_k()
        self.current_beta_array = SU.reusing_work_update(
            self.current_beta_array,
            z_j,
            random_challenge,
            self.get_p(),
        )
        return

    def reusing_work_beta_get(self, z_j: int, t: int):
        """
        This function returns the beta value at the step and input.
        INPUTS:
        step is the step number we are currently at. t is the value we are looking for. Typically t is 0/1/2/3.
        OUTPUT:
        This function returns a value of beta.

        This function is different from reusing_work_beta_update in that it accepts t typically equal to 0/1/2/3, and it doesn't change the array stored in the prover instance.
        """
        # k = self.get_k()
        # depth = self.get_depth()
        result_tuple = SU.reusing_work_update(
            self.current_beta_array,
            z_j,
            t,
            self.get_p(),
        )
        return result_tuple

    def sum_fi_parallel(self, layer: int, step: int):
        """
        Based on our verification, the optimized parallelism proposed by us does not apply itself to mult layer. We need to use the original data parallelism to support mult layer.
        """
        circ = self.get_circ()
        d = circ.get_depth()
        p = circ.get_p()
        k = circ.get_k()
        copy_k = circ.get_copy_k()
        num_copy = circ.get_num_copy()
        assert layer >= 0 and layer < d, "i is out of bounds"
        assert layer < len(self.get_random_vectors()), "haven't reached this layer yet"
        # the partial sumcheck function address the case of s=0.
        assert (
            1 <= step <= k[layer] + 2 * (k[layer + 1] - num_copy[layer])
        ), "In parallel settings, the step s in sumcheck is out of bounds"
        # check the len and type of RV
        assert isinstance(
            self.get_random_vector(layer), tuple
        ), f"RV must be a tuple, but got {type(self.get_random_vector(layer))}"
        assert (
            len(self.get_random_vector(layer)) == k[layer]
        ), f"RV must have {k[layer]} elements, but got {len(self.get_random_vector(layer))}"

        # variable step can range from 0 to k[i]+2*(copy_k[i+1]).
        # Iteration of step can be separated into 4 parts, corresponding to gradually determining a_1, b_1, c_1 and a_2.
        # When determining a_1, b_1 and a_2, in every step, we need to do a streaming pass over all of the gate in a copy.
        # When determining a_2, mult is already fixed.
        current_random_elements = self.get_layer_i_sumcheck_random_elements(layer)
        # bc_partial is of length step - 1. It needs to append 0/1/2/3 to the final length step list.
        bc_partial = tuple(current_random_elements[: step - 1])
        this_layer_random_vector = self.get_random_vector(layer)
        # this_layer_random_vector is separated into z1, gate label and z2, copy label.
        z2 = this_layer_random_vector[: num_copy[layer]]
        z1 = this_layer_random_vector[num_copy[layer] :]
        W_iplus1 = circ.get_W(layer + 1)
        # We assume poly_values has 4 elements. In add layer, we only pass the first 3 elements.
        poly_values = [0, 0, 0, 0]
        if layer == d - 1:
            degree = 4
        else:
            degree = 3
        # @ 1. 1<=s<=copy_k[layer] fixing a_1
        if step <= copy_k[layer]:
            assert len(self.current_beta_array) == 2 ** (
                k[layer] - step + 1
            ), f"current_beta_array must have {2**(
                k[layer] - step + 1
            )} elements, but got {len(self.current_beta_array)}"
            beta_array_0 = self.reusing_work_beta_get(z1[step - 1], 0)
            beta_array_1 = self.reusing_work_beta_get(z1[step - 1], 1)
            beta_array_2 = self.reusing_work_beta_get(z1[step - 1], 2)
            if layer == d - 1:
                beta_array_3 = self.reusing_work_beta_get(z1[step - 1], 3)
            for gate in range(2 ** copy_k[layer]):
                # gate_inputs, a_gate, b1, c1 are all independent of x.
                gate_inputs = circ.get_inputs(layer, gate)
                a_gate = (
                    SU.int_to_bin(gate, copy_k[layer])
                    + SU.int_to_bin(gate_inputs[0], k[layer + 1] - num_copy[layer])
                    + SU.int_to_bin(gate_inputs[1], k[layer + 1] - num_copy[layer])
                )
                b1 = a_gate[
                    copy_k[layer] : copy_k[layer] + k[layer + 1] - num_copy[layer]
                ]
                c1 = a_gate[k[layer + 1] - num_copy[layer] + copy_k[layer] :]
                assert (
                    len(b1) == len(c1) and len(b1) == k[layer + 1] - num_copy[layer]
                ), "b1 and c1 must have the same length, and b1 must have length copy_k[layer+1]-num_copy[layer]"
                # mult_chi is the tilde mult value in this step.
                mult_chi = [0] * degree
                for x in range(degree):
                    a1 = (
                        (x,)
                        if copy_k[layer] == 1
                        else bc_partial + (x,) + a_gate[step : copy_k[layer]]
                    )
                    # When s==1, mult_chi is left with only the a1 part, while the rest evaluates to 1.
                    mult_chi[x] = SU.chi(a1, a_gate[: copy_k[layer]], copy_k[layer], p)
                assert len(mult_chi) == degree, f"mult_chi must have length {degree}"
                for copy in range(2 ** num_copy[layer]):
                    a2 = SU.int_to_bin(copy, num_copy[layer])
                    final_beta = [
                        beta_array_0[copy],
                        beta_array_1[copy],
                        beta_array_2[copy],
                    ]
                    if layer == d - 1:
                        final_beta.append(beta_array_3[copy])
                    W_iplus1_b = W_iplus1[(a2 + b1)]
                    W_iplus1_c = W_iplus1[(a2 + c1)]
                    for x in range(degree):
                        poly_values[x] = (
                            poly_values[x]
                            + final_beta[x] * mult_chi[x] * W_iplus1_b * W_iplus1_c
                        ) % p
        # @ 2. copy_k[layer] < s <= copy_k[layer]+k[layer+1]-num_copy[layer], fixing b_1
        elif copy_k[layer] < step <= copy_k[layer] + k[layer + 1] - num_copy[layer]:
            assert len(self.current_beta_array) == 2 ** (
                num_copy[layer]
            ), f"current_beta_array must have {2**(
                num_copy[layer]
            )} elements, but got {len(self.current_beta_array)}"
            a1 = bc_partial[: copy_k[layer]]
            # beta_array keeps the same in this process. No need to update it.
            for gate in range(2 ** copy_k[layer]):
                # gate_inputs, a_gate, b1, c1 are all independent of x.
                gate_inputs = circ.get_inputs(layer, gate)
                a_gate = (
                    SU.int_to_bin(gate, copy_k[layer])
                    + SU.int_to_bin(gate_inputs[0], k[layer + 1] - num_copy[layer])
                    + SU.int_to_bin(gate_inputs[1], k[layer + 1] - num_copy[layer])
                )
                c1 = a_gate[k[layer + 1] - num_copy[layer] + copy_k[layer] :]
                mult_chi = [0] * degree
                for x in range(degree):
                    b1 = (
                        bc_partial[copy_k[layer] :]
                        + (x,)
                        + a_gate[step : copy_k[layer] + k[layer + 1] - num_copy[layer]]
                    )
                    assert (
                        len(b1) == len(c1) and len(b1) == k[layer + 1] - num_copy[layer]
                    ), "b1 and c1 must have the same length, and b1 must have length copy_k[layer+1]-num_copy[layer]"
                    mult_chi[x] = SU.chi(
                        a1 + b1[: step - copy_k[layer]],
                        a_gate[:step],
                        step,
                        p,
                    )
                    for copy in range(2 ** num_copy[layer]):
                        a2 = SU.int_to_bin(copy, num_copy[layer])
                        # W_iplus1_b = SU.Cormode_eval_W(
                        #     W_iplus1,
                        #     a2
                        #     + b1[: step - copy_k[layer]]
                        #     + a_gate[
                        #         step : copy_k[layer] + k[layer + 1] - num_copy[layer]
                        #     ],
                        #     num_copy[layer] + step - copy_k[layer],
                        #     k[layer + 1],
                        #     p,
                        # )
                        W_iplus1_b = SU.DP_eval_MLE(
                            W_iplus1,
                            a2
                            + b1[: step - copy_k[layer]]
                            + a_gate[
                                step : copy_k[layer] + k[layer + 1] - num_copy[layer]
                            ],
                            k[layer + 1],
                            p,
                        )
                        W_iplus1_c = W_iplus1[(a2 + c1)]
                        poly_values[x] = (
                            poly_values[x]
                            + self.current_beta_array[copy]
                            * mult_chi[x]
                            * W_iplus1_b
                            * W_iplus1_c
                        ) % p
        # @ 3. copy_k[layer]+k[layer+1]-num_copy[layer]+1 <= step <= copy_k[layer]+2*(k[layer+1]-num_copy[layer]), fixing c_1
        elif (
            copy_k[layer] + k[layer + 1] - num_copy[layer] + 1
            <= step
            <= copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer])
        ):
            # beta_array keeps the same.
            assert len(self.current_beta_array) == 2 ** (
                num_copy[layer]
            ), f"current_beta_array must have {2**(
                num_copy[layer]
            )} elements, but got {len(self.current_beta_array)}"
            # both a1 and b1 are fixed in this process.
            a1 = bc_partial[: copy_k[layer]]
            b1 = bc_partial[
                copy_k[layer] : copy_k[layer] + k[layer + 1] - num_copy[layer]
            ]
            # beta_array keeps the same in this process. No need to update it.
            for gate in range(2 ** copy_k[layer]):
                # gate_inputs, a_gate, b1, c1 are all independent of x.
                gate_inputs = circ.get_inputs(layer, gate)
                a_gate = (
                    SU.int_to_bin(gate, copy_k[layer])
                    + SU.int_to_bin(gate_inputs[0], k[layer + 1] - num_copy[layer])
                    + SU.int_to_bin(gate_inputs[1], k[layer + 1] - num_copy[layer])
                )
                mult_chi = [0] * degree
                for x in range(degree):
                    c1 = (
                        bc_partial[copy_k[layer] + k[layer + 1] - num_copy[layer] :]
                        + (x,)
                        + a_gate[step:]
                    )
                    assert (
                        len(b1) == len(c1) and len(b1) == k[layer + 1] - num_copy[layer]
                    ), "b1 and c1 must have the same length, and b1 must have length copy_k[layer+1]-num_copy[layer]"
                    mult_chi[x] = SU.chi(
                        a1
                        + b1
                        + c1[: step - (copy_k[layer] + k[layer + 1] - num_copy[layer])],
                        a_gate[:step],
                        step,
                        p,
                    )
                    for copy in range(2 ** num_copy[layer]):
                        a2 = SU.int_to_bin(copy, num_copy[layer])
                        # W_iplus1_b = SU.Cormode_eval_W(
                        #     W_iplus1,
                        #     a2
                        #     + b1[: step - copy_k[layer]]
                        #     + a_gate[
                        #         step : copy_k[layer] + k[layer + 1] - num_copy[layer]
                        #     ],
                        #     num_copy[layer] + step - copy_k[layer],
                        #     k[layer + 1],
                        #     p,
                        # )
                        W_iplus1_b = SU.DP_eval_MLE(
                            W_iplus1,
                            a2 + b1,
                            k[layer + 1],
                            p,
                        )
                        W_iplus1_c = SU.DP_eval_MLE(
                            W_iplus1,
                            a2 + c1,
                            k[layer + 1],
                            p,
                        )
                        poly_values[x] = (
                            poly_values[x]
                            + self.current_beta_array[copy]
                            * mult_chi[x]
                            * W_iplus1_b
                            * W_iplus1_c
                        ) % p

        # @ 4. step > copy_k[layer]+2*(k[layer+1]-num_copy[layer]), fixing a_2
        elif step > copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]):
            assert len(self.current_beta_array) == 2 ** (
                num_copy[layer]
                - (step - (copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 1))
            ), f"current_beta_array must have {2**(
                num_copy[layer] - (step - (copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 1))
            )} elements, but got {len(self.current_beta_array)}"
            beta_array_0 = self.reusing_work_beta_get(
                z2[step - (copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 1)], 0
            )
            beta_array_1 = self.reusing_work_beta_get(
                z2[step - (copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 1)], 1
            )
            beta_array_2 = self.reusing_work_beta_get(
                z2[step - (copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 1)], 2
            )
            if layer == d - 1:
                beta_array_3 = self.reusing_work_beta_get(
                    z2[
                        step
                        - (copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 1)
                    ],
                    3,
                )
            a1 = bc_partial[: copy_k[layer]]
            b1 = bc_partial[
                copy_k[layer] : copy_k[layer] + k[layer + 1] - num_copy[layer]
            ]
            c1 = bc_partial[
                copy_k[layer]
                + k[layer + 1]
                - num_copy[layer] : copy_k[layer]
                + 2 * (k[layer + 1] - num_copy[layer])
            ]
            mult_chi = circ.eval_MLE_mult(layer, a1 + b1 + c1)
            for x in range(degree):
                # a2_partial is of length s-5 in our case, s-len(a1)-len(b1)-len(c1) in general.
                a2_partial = bc_partial[
                    copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) :
                ] + (x,)
                for copy_partial in range(
                    2
                    ** (
                        num_copy[layer]
                        - (
                            step
                            - (copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]))
                        )
                    )
                ):
                    a2 = a2_partial + SU.int_to_bin(
                        copy_partial,
                        num_copy[layer]
                        - (
                            step
                            - (copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]))
                        ),
                    )
                    if x == 0:
                        beta_value = beta_array_0[copy_partial]
                    elif x == 1:
                        beta_value = beta_array_1[copy_partial]
                    elif x == 2:
                        beta_value = beta_array_2[copy_partial]
                    elif x == 3:
                        beta_value = beta_array_3[copy_partial]
                    else:
                        raise ValueError("x must be 0, 1, 2 or 3, but got {}".format(x))
                    W_iplus1_b = SU.DP_eval_MLE(
                        W_iplus1,
                        a2 + b1,
                        k[layer + 1],
                        p,
                    )
                    W_iplus1_c = SU.DP_eval_MLE(
                        W_iplus1,
                        a2 + c1,
                        k[layer + 1],
                        p,
                    )
                    poly_values[x] = (
                        poly_values[x] + beta_value * mult_chi * W_iplus1_b * W_iplus1_c
                    ) % p
        if layer == d - 1:
            poly = SU.cubic_interpolate(poly_values, p)
        else:
            poly = SU.quadratic_interpolate(poly_values, p)
        return poly

    def partial_sumcheck(self, i: int, s: int, random_element: int):
        """
        partial_sumcheck
        INPUT: i (integer), s (integer), random_element (integer)
        OUTPUT: poly (list)

        performs step s of sumcheck for layer i of the circuit.
        here, sumcheck is done with respect to the polynomial in Eq. 4.17 (section 4.6.3: Protocol overview)
        of Thaler's book. this polynomial, which we will call f^{i}_{r_i}, is a polynomial in
        2 * k[i] variables
        i is the layer in the circuit, s is the step in the sumcheck protocol
        random_element is the random element of F_p that the verifier sends. (in case of the first communication, we'll  default this to 0.)
        copy_number is the number of copies of the circuit that we are using. For now we assume the whole circuit conform to one assignment.
        returns a quadratic polynomial in the form [a, b, c], which corresponds to
        a + bx + cx^2

        The above sum_fi function can do most work of this, but we need to encapsulate that function. Here different actions are taken depending on the step s.
        """
        d = self.d
        k = self.k
        num_copy = self.get_circ().get_num_copy()
        copy_k = self.get_circ().get_copy_k()
        assert i >= 0 and i < d, "i is out of bounds"

        assert s >= 0 and s <= 2 * (
            k[i + 1] - num_copy[i]
        ), f"In parallel settings, step must be between 0 and 2*copy_k_{i+1}. Now s={s}, copy_k_{i+1}={copy_k[i+1]}"

        # Now protocol starts. RV_i is the input to the claim at this layer. In detail, every layer, the claim starts with W_i(random vector)=claimed value. RV_i here is the random vector.
        RV_i = self.get_random_vector(i)

        # at step = 0 of the sumcheck about W_i and W_i+1, we are starting the sumcheck protocol and
        # have to send back the actual value of
        # \tilde{W}_i(value_of_random_vectors[i]).
        # (NOTE: no sum is required.)
        if s == 0:
            new_evaluation = self.get_evaluation_of_RV(i)
            if DEBUG_INFO:
                print(
                    "The multi-linear extension of W_{} at {} is {}".format(
                        i, RV_i, new_evaluation
                    )
                )
            return [new_evaluation, 0, 0]

        # from s==1, Prover has to send the partial sum of the W_i+1 variables. But until now no random element has been sent from verifier to prover, so we don't need to append the random_element to the SRE.
        elif s == 1:
            poly = self.sum_fi(i, s)
            self.append_sumcheck_polynomial(i, poly)
            return poly
        elif s <= 2 * (k[i + 1] - num_copy[i]):
            # the sumcheck_random_elements[i] keeps updating as we use every round. It initializes to all 0 but every time we only use its non-zero part after update.
            self.append_element_SRE(i, random_element)
            poly = self.sum_fi(i, s)
            self.append_sumcheck_polynomial(i, poly)
            return poly

    # NOTE: we're appending the last random element, to fill out the sumcheck random elements. Write in specs!

    def partial_sumcheck_parallel(self, layer: int, step: int, random_element: int):
        """
        In the naive_parallelism branch, this function is used throughout all of the layers in the circuit.
        """
        d = self.get_depth()
        k = self.get_k()
        num_copy = self.get_num_copy()
        copy_k = self.get_copy_k()
        RV_i = self.get_random_vector(layer)
        if step == 0:
            new_evaluation = self.get_evaluation_of_RV(layer)
            if DEBUG_INFO:
                print(
                    "The multi-linear extension of W_{} at {} is {}".format(
                        layer, RV_i, new_evaluation
                    )
                )
            return [new_evaluation, 0, 0]
        if step == 1:
            self.current_beta_array = self.reusing_work_beta_initialize(
                layer, self.get_random_vector(layer)
            )
            poly = self.sum_fi_parallel(layer, step)
            self.append_sumcheck_polynomial(layer, poly)
            return poly
        # step == 2 means a_1 is fixed(we assume a_1 is 1 bit). for now the beta keeps the same until a_2 round.
        if step == 2:
            # update beta array
            self.reusing_work_beta_update(
                self.get_random_vector(layer)[-1], random_element
            )
            self.append_element_SRE(layer, random_element)
            poly = self.sum_fi_parallel(layer, step)
            self.append_sumcheck_polynomial(layer, poly)
            return poly
        # when step == copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 1, we are actually fixing a_2, but since we don't need to update the beta array, the code is the same as previous situations.
        if 3 <= step <= copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 1:
            self.append_element_SRE(layer, random_element)
            poly = self.sum_fi_parallel(layer, step)
            self.append_sumcheck_polynomial(layer, poly)
            return poly
        if (
            copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 1
            < step
            <= k[layer] + 2 * (k[layer + 1] - num_copy[layer])
        ):
            self.reusing_work_beta_update(
                self.get_random_vector(layer)[
                    step - (copy_k[layer] + 2 * (k[layer + 1] - num_copy[layer]) + 2)
                ],
                random_element,
            )
            self.append_element_SRE(layer, random_element)
            poly = self.sum_fi_parallel(layer, step)
            self.append_sumcheck_polynomial(layer, poly)
            return poly
        assert (
            False
        ), f"step must be between 0 and {k[layer] + 2 * (k[layer + 1] - num_copy[layer + 1])}, but got {step}"

    def send_Wi_on_line(self, i: int, random_element: int):
        """
        send_Wi_on_line
        INPUTS: i (integer), random_element (integer)
        outputs: poly (list)
        At the end of the layer i sumcheck protocol, the Prover must send the
        polynomial \tilde{W}_{i} on the line between bstar and cstar that both
        the prover and the verifier independently compute. (This is implemented
        in the Interactor class.)
        On input i (layer #) and random_element (the last randomness that the
        Verifier sends), we append the random_element to our SRE, and then compute
        the univariate polynomial poly that is \tilde{W}_i|_{line}.

        NOTE: we have to append the random_element because in our implementation,
        when the verifier sends a random element, only in the next call of partial sumcheck does the
        prover add it to its internal state. But since it's the end there is no next call.
        """
        # z_tuple is the z1 and z2.
        z_tuple = self.get_random_vector(i)
        p = self.get_p()
        k = self.get_k()
        # copy_k = self.get_circ().get_copy_k()
        num_copy = self.get_num_copy()

        # After appending, there are only 2*copy_k[i+1] elements in the SRE.
        self.append_element_SRE(i, random_element)
        # We need to expand it to 2*k[i+1]
        if not i == self.get_depth() - 1:
            self.process_SRE_for_parallelism(i, z_tuple[: num_copy[i]])
        else:
            self.process_SRE_for_parallelism(
                i, tuple(self.get_sumcheck_random_elements()[-1][-num_copy[i] :])
            )
        # line is a function taking input an integer.
        line = self.compute_line(i)
        self.append_line(line)
        W_iplus1 = self.circ.get_W(i + 1)
        # The polynomial sent, W_i+1(l) is at most k_i+1
        poly = SU.polynomial_interpolation(
            [
                [N, SU.DP_eval_MLE(W_iplus1, line(N), k[i + 1], p)]
                for N in range(k[i + 1] + 1)
            ],
            k[i + 1],
            p,
        )
        return poly

    def send_final_Wd_evaluation(self):
        """
        send_final_Wd_evaluation
        OUTPUT: \tilde{W}_d(random_vector[d])
        This is what the prover's sends at the end of the protocol: it is
        the value of \tilde{W}_d (i.e., the MLE of the input) on the random vector that
        has been generated by the protocol.
        """
        d = self.get_depth()
        return self.get_evaluation_of_RV(d)
