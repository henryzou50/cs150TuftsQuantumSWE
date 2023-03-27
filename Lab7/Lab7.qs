// Intro to Quantum Software Development
// Lab 7: Grover's Search Algorithm
// Copyright 2023 The MITRE Corporation. All Rights Reserved.
//
// Due 3/27 at 6:00PM ET:
//  - Completed exercises and evidence of unit tests passing uploaded to GitHub.

namespace Lab7 {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Measurement;


    /// # Summary
    /// In this exercise, you are given a classical bit array and a qubit
    /// register. Both are of unknown length, but they have the same length.
    /// Your goal is to apply the bitwise XOR operation in-place on the
    /// quantum register, using its own state and the classical bit array as
    /// the two input arguments, and using the register itself as the output.
    /// For example, if the classical bit array is 10110 and the qubit
    /// register is in the state |00101>, then this operation should put the
    /// qubit register into the state 10110 XOR 00101 = |10011>.
    ///
    /// # Input
    /// ## classicalBits
    /// A classical bit array that contains an unknown bit string of unknown
    /// length.
    ///
    /// ## register
    /// A qubit array in an unknown state, which has the same length as the
    /// classicalBits array.
    ///
    /// # Remarks
    /// This operation must support the ability to be called in Adjoint mode,
    /// which means it can only reversible operations.
    operation Exercise1_XOR (classicalBits : Bool[], register : Qubit[]) : Unit
    is Adj {
        for idx in 0 .. Length(classicalBits) - 1 {
            if (classicalBits[idx]) {
                X(register[idx]);
            }
        }
    }


    /// # Summary
    /// In this exercise, you must implement an oracle that checks if all of
    /// the provided qubits are in the |0> state. You are given a qubit
    /// register of unknown length in an unknown state, and a target qubit
    /// that is in the |1> state. Your goal is to phase-flip the target qubit
    /// if the register is in the state |0...0>.
    ///
    /// # Input
    /// ## register
    /// A register of unknown length in an unknown state.
    ///
    /// ## target
    /// The target qubit that you must phase-flip if the register is in the
    /// |0...0> state. The target qubit will be provided in the |1> state.
    operation Exercise2_CheckIfAllZeros (
        register : Qubit[],
        target : Qubit
    ) : Unit {
    ApplyToEach(X, register);
    Controlled Z(register, target);
    ApplyToEach(X, register);
}


    /// # Summary
    /// In this exercise, you must implement an oracle that checks to see if a
    /// provided encryption key is correct. You are given an original message
    /// as a classical bit string and the message after it has been encrypted
    /// with an unknown encryption key. The encryption algorithm is a bitwise
    /// XOR. You are also given a qubit register which represents the
    /// encryption key being checked, and a target qubit. Your goal is to
    /// phase-flip the target qubit if the state of the qubit register
    /// corresponds to the encryption key that was used to encrypt the
    /// original message.
    ///
    /// # Input
    /// ## originalMessage
    /// A classical bitstring containing the original message that was
    /// encrypted.
    ///
    /// ## encryptedMessage
    /// A classical bitstring containing the original message after it was
    /// encrypted with a bitwise XOR algorithm.
    ///
    /// ## candidateEncryptionKey
    /// A quantum register containing the potential encryption key that is
    /// being checked by your oracle - think of it like a quantum version of
    /// the classical encryption key.
    ///
    /// ## target
    /// The qubit that you should phase-flip if the candidate key is the
    /// correct key - that is, if encrypting the original message with it
    /// produces the same bitstring as the encryptedMessage bitstring.
    ///
    /// # Remarks
    /// Obviously, bitwise XOR is a trivial example because you can just XOR
    /// the original message with the encrypted message to recover the
    /// encryption key. The point of this exercise is to show that this
    /// process can be done with any algorithm, including ones that are
    /// nontrivial like modern cryptographic ciphers (SHA256, AES, etc.). XOR
    /// is just used here because it's easy to implement, think of it as a
    /// proof-of-concept.
    operation Exercise3_CheckKey (
        originalMessage : Bool[],
        encryptedMessage : Bool[],
        candidateEncryptionKey : Qubit[],
        target : Qubit
    ) : Unit {
        // Hint: you can use your Exercise 1 implementation to perform the XOR
        // operation, compare the qubit register to the encrypted message, and
        // then run Exercise1 in Adjoint mode to put the register back into
        // its original state.

        let len = Length(encryptedMessage) - 1;
        for idx in 0 .. len {
            if encryptedMessage[idx] == false {
                X(candidateEncryptionKey[idx]);
            }
        }

        Exercise1_XOR(originalMessage, candidateEncryptionKey);
        Controlled Z(candidateEncryptionKey, target);

        for idx in 0 .. len {
            if encryptedMessage[idx] == false {
                X(candidateEncryptionKey[idx]);
            }
        }

        Adjoint Exercise1_XOR(originalMessage, candidateEncryptionKey);

    }


    /// # Summary
    /// In this exercise, you must implement the repeated quantum iteration in
    /// Grover's algorithm, which consists of running the oracle and then the
    /// diffusion operator. You are given an oracle to run, a qubit register
    /// representing the input to the oracle, and a target qubit that the
    /// oracle can use for phase-flipping if provided with the correct input.
    ///
    /// # Input
    /// ## oracle
    /// A function object representing the oracle being used during the search
    /// to find the "correct" state. You can run it with the following syntax:
    ///     oracle(Register, Target);
    ///
    /// ## register
    /// A qubit register of unknown length and unknown state. This represents
    /// the input you should provide to the oracle.
    ///
    /// ## target
    /// A qubit in the |1> state. This represents a target you can use for any
    /// phase-flipping oracles.
    ///
    /// # Remarks
    /// The unit test for Exercises4 uses the previous exercises, so make sure
    /// those pass for attempting this one.
    operation Exercise4_GroverIteration (
        oracle : (Qubit[], Qubit) => Unit,
        register : Qubit[],
        target : Qubit
    ) : Unit {
        oracle(register, target);
        ApplyToEach(H, register);
        ApplyToEach(X, register);
        Controlled Z(register, target);
        ApplyToEach(X, register);
        ApplyToEach(H, register);
    }


    /// # Summary
    /// In this exercise, you must implement Grover's quantum search
    /// algorithm. You have already implemented all of the pieces, so now you
    /// just need to put them all together. You are given an oracle which can
    /// correctly identify the "correct" answer to the problem being searched,
    /// and a number of qubits that it expects for its input register. Your
    /// goal is to use this information to run Grover's search and find the
    /// correct state.
    ///
    /// # Input
    /// ## oracle
    /// A phase-flipping operation that can identify the "correct" answer to a
    /// problem by giving it a negative amplitude.
    ///
    /// ## numberOfQubits
    /// The number of qubits that the oracle expects in its input register.
    ///
    /// # Output
    /// You must return a classical bit string (false for 0, true for 1) that
    /// represents the solution that the search algorithm found.
    operation Exercise5_GroverSearch (
        oracle : (Qubit[], Qubit) => Unit,
        numberOfQubits : Int
    ) : Bool[] {
        // This calculates the number of iterations you should run during the
        // Grover search. It's provided here for your convenience.
        let iterations = Round(PI() / 4.0 * Sqrt(IntAsDouble(numberOfQubits)));

        use register = Qubit[numberOfQubits];
        use target = Qubit();
        ApplyToEach(H, register);
        X(target);

        for idx in 0 .. iterations {
            Exercise4_GroverIteration(
                oracle,
                register,
                target
            );
        }

        mutable output = [];
        for idx in 0 .. numberOfQubits - 1 {
            set output += ResultArrayAsBoolArray([M(register[idx])]);
        }

        if M(target) == One {
            X(target);
        }
        ResetAll(register);

        return output;
    }
}
