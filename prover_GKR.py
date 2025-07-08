#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Jul 18 20:58:15 2022

@author: raju
"""


from interactor_GKR import Interactor

import sumcheck_util as SU
import circuit

DEBUG_INFO = True


class Prover(Interactor):
    """
    Prover class is a subclass of the interactor. Given the base interactor, we also
    compute the circuit. There are no extra internal variables.
    """

    def __init__(self, C: circuit):
        Interactor.__init__(self, C)
        # Prover needs to compute the circuit. This is done once initialized.
        self.circ.compute_circuit()

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
        evaluation_at_random_vector = SU.eval_MLE(D_i, r_i, k[i], p)
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
        copy_k = self.get_copy_k()
        num_copy = k[0] - copy_k[0]
        assert i >= 0 and i < d, "i is out of bounds"
        assert i < len(self.get_random_vectors()), "haven't reached this layer yet"
        # the partial sumcheck function address the case of s=0.
        assert (
            s >= 1 and s <= 2 * copy_k[i + 1]
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
        # z1 is the gate random, z1 is of length copy_k[i].
        z1 = self.get_random_vector(i)[-copy_k[i] :]
        # z2 is the copy random, z2 is of length k[i] - copy_k[i].
        z2 = self.get_random_vector(i)[: -copy_k[i]]
        # Initialize variables that might be used later
        Cormode_b_0 = None
        Cormode_b_1 = None
        Cormode_b_2 = None
        Cormode_c = None
        Cormode_c_0 = None
        Cormode_c_1 = None
        Cormode_c_2 = None

        # First case, [1, copy_k[i + 1]). Use cormode for b in every s and Cormode for c once for all s.
        if s < copy_k[i + 1]:
            # b: Cormode c: all binary, directly retrieve
            # Cormode_b takes in length copy_k[i+1]-s
            Cormode_b_0 = SU.Cormode_eval_W(
                W_iplus1, z2 + bc_partial + (0,), s + num_copy, k[i + 1], p
            )
            Cormode_b_1 = SU.Cormode_eval_W(
                W_iplus1, z2 + bc_partial + (1,), s + num_copy, k[i + 1], p
            )
            Cormode_b_2 = SU.Cormode_eval_W(
                W_iplus1, z2 + bc_partial + (2,), s + num_copy, k[i + 1], p
            )
            # Cormode_c can be optimized. when s<copy_k[i+1], Cormode_c is always the same. But Now I have no idea how to optimize it.
            # Cormode_c takes in length copy_k[i+1]
            Cormode_c = SU.Cormode_eval_W(
                W_iplus1, z2, k[i + 1] - copy_k[i + 1], k[i + 1], p
            )
        # Second case, s == copy_k[i + 1]. b is calculated by MLE eval, while c is calculated with the same Cormode as above.
        elif s == copy_k[i + 1]:
            Cormode_c = SU.Cormode_eval_W(
                W_iplus1, z2, k[i + 1] - copy_k[i + 1], k[i + 1], p
            )
        # Third case, B is still calculated by MLE, C is calculated by Cormode per step.
        elif copy_k[i + 1] < s < 2 * copy_k[i + 1]:
            partial_input_to_c_0 = z2 + bc_partial[copy_k[i + 1] : s - 1] + (0,)
            partial_input_to_c_1 = z2 + bc_partial[copy_k[i + 1] : s - 1] + (1,)
            partial_input_to_c_2 = z2 + bc_partial[copy_k[i + 1] : s - 1] + (2,)
            Cormode_c_0 = SU.Cormode_eval_W(
                W_iplus1,
                partial_input_to_c_0,
                s + num_copy - copy_k[i + 1],
                k[i + 1],
                p,
            )
            Cormode_c_1 = SU.Cormode_eval_W(
                W_iplus1,
                partial_input_to_c_1,
                s + num_copy - copy_k[i + 1],
                k[i + 1],
                p,
            )
            Cormode_c_2 = SU.Cormode_eval_W(
                W_iplus1,
                partial_input_to_c_2,
                s + num_copy - copy_k[i + 1],
                k[i + 1],
                p,
            )
        else:
            pass
        # The Cormode evaluation should be done before going into each specific gate.
        for gate in range(2 ** copy_k[i]):
            # we use the first copy as an example.
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
            # a_gate is of length copy_k[i] + 2 * copy_k[i + 1].
            a_gate = (
                a[num_copy : k[i]]
                + a[k[i] + num_copy : k[i] + k[i + 1]]
                + a[k[i] + k[i + 1] + num_copy :]
            )
            for x in range(3):

                # No matter in which case, we all get poly_values[x] filled
                gate_type = circ.get_type(i, gate)
                if s < copy_k[i + 1]:
                    # b: Cormode c: all binary, directly retrieve
                    if x == 0:
                        W_iplus1_at_b = Cormode_b_0[
                            SU.tuple_to_int(
                                a_gate[copy_k[i] + s : copy_k[i] + copy_k[i + 1]]
                            )
                        ]
                    elif x == 1:
                        W_iplus1_at_b = Cormode_b_1[
                            SU.tuple_to_int(
                                a_gate[copy_k[i] + s : copy_k[i] + copy_k[i + 1]]
                            )
                        ]
                    elif x == 2:
                        W_iplus1_at_b = Cormode_b_2[
                            SU.tuple_to_int(
                                a_gate[copy_k[i] + s : copy_k[i] + copy_k[i + 1]]
                            )
                        ]
                    else:
                        raise ValueError("x must be 0, 1 or 2, but got {}".format(x))

                    W_iplus1_at_c = Cormode_c[
                        SU.tuple_to_int(a_gate[copy_k[i] + copy_k[i + 1] :])
                    ]

                elif s == copy_k[i + 1]:
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
                    else:
                        raise ValueError("x must be 0, 1 or 2, but got {}".format(x))

                    W_iplus1_at_c = Cormode_c[
                        SU.tuple_to_int(a_gate[copy_k[i] + copy_k[i + 1] :])
                    ]

                elif copy_k[i + 1] < s < 2 * copy_k[i + 1]:
                    # b: all FFE c: Cormode, directly retrieve
                    W_iplus1_at_b = SU.DP_eval_MLE(
                        W_iplus1, z2 + bc_partial[: copy_k[i + 1]], k[i + 1], p
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
                    else:
                        raise ValueError("x must be 0, 1 or 2, but got {}".format(x))

                elif s == 2 * copy_k[i + 1]:
                    W_iplus1_at_b = SU.DP_eval_MLE(
                        W_iplus1, z2 + bc_partial[: copy_k[i + 1]], k[i + 1], p
                    )

                    if x == 0:
                        W_iplus1_at_c = SU.DP_eval_MLE(
                            W_iplus1,
                            z2 + bc_partial[copy_k[i + 1] :] + (0,),
                            k[i + 1],
                            p,
                        )
                    elif x == 1:
                        W_iplus1_at_c = SU.DP_eval_MLE(
                            W_iplus1,
                            z2 + bc_partial[copy_k[i + 1] :] + (1,),
                            k[i + 1],
                            p,
                        )
                    elif x == 2:
                        W_iplus1_at_c = SU.DP_eval_MLE(
                            W_iplus1,
                            z2 + bc_partial[copy_k[i + 1] :] + (2,),
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
                            z1 + bc_partial + (x,),
                            copy_k[i] + s,
                            p,
                        )
                        * (W_iplus1_at_b + W_iplus1_at_c)
                    ) % p
                elif gate_type == "mult":
                    print("mult gate")
                    poly_values[x] = (
                        poly_values[x]
                        + SU.chi(
                            a_gate[: copy_k[i] + s],
                            z1 + bc_partial + (x,),
                            copy_k[i] + s,
                            p,
                        )
                        * (W_iplus1_at_b * W_iplus1_at_c)
                    ) % p
                # W_iplus1_at_b = SU.DP_eval_MLE(W_iplus1, b, k[i + 1], p)
                # W_iplus1_at_c = SU.DP_eval_MLE(W_iplus1, c, k[i + 1], p)
                # gate_type = circ.get_type(i, gate)
                # This is the Tormode method. Each gate only contribute to one term, so we can just iterate over the gates. This also reduce the need to evaluate add and mult.
                # if gate_type == "add":
                #     poly_values[x] = (
                #         poly_values[x]
                #         + SU.chi(a, z, N, p) * (W_iplus1_at_b + W_iplus1_at_c)
                #     ) % p
                # elif gate_type == "mult":
                #     poly_values[x] = (
                #         poly_values[x]
                #         + SU.chi(a, z, N, p) * (W_iplus1_at_b * W_iplus1_at_c)
                #     ) % p
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
        # k = self.k
        copy_k = self.get_copy_k()
        assert i >= 0 and i < d, "i is out of bounds"

        assert (
            s >= 0 and s <= 2 * copy_k[i + 1]
        ), "In parallel settings, step must be between 0 and 2*copy_k_{i+1}"

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
        elif s <= 2 * copy_k[i + 1]:
            # the sumcheck_random_elements[i] keeps updating as we use every round. It initializes to all 0 but every time we only use its non-zero part after update.
            self.append_element_SRE(i, random_element)
            poly = self.sum_fi(i, s)
            self.append_sumcheck_polynomial(i, poly)
            return poly

    # NOTE: we're appending the last random element, to fill out the sumcheck random elements. Write in specs!

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
        copy_k = self.get_copy_k()
        # num_copy = self.get_num_copy()

        # After appending, there are only 2*copy_k[i+1] elements in the SRE.
        self.append_element_SRE(i, random_element)
        # We need to expand it to 2*k[i+1]
        self.process_SRE_for_parallelism(i, z_tuple[: -copy_k[i]])
        # line is a function taking input an integer.
        line = self.compute_line(i)
        self.append_line(line)
        W_iplus1 = self.circ.get_W(i + 1)
        # The polynomial sent, W_i+1(l) is at most k_i+1
        poly = SU.polynomial_interpolation(
            [
                [N, SU.eval_MLE(W_iplus1, line(N), k[i + 1], p)]
                for N in range(k[i + 1] + 1)
            ],
            k[i + 1],
            p,
        )
        # deg_of_poly = len(poly)-1
        # string_of_poly = "+".join(\
        #                           ["{}*x^{}".format(poly[k],deg_of_poly - k) for k in range(deg_of_poly+1)])
        # print("The univariate polynomial that the prover sends at the end of step {} on the line is: {}".\
        #       format(i, string_of_poly))
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
