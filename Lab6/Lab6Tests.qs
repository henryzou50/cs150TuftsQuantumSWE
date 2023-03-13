// QSD Lab 6 Q# Tests
// Copyright 2023 The MITRE Corporation. All Rights Reserved.
//
// DO NOT MODIFY THIS FILE.

namespace Lab6 {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Random;


    @Test("QuantumSimulator")
    operation Exercise1Test () : Unit {
        for numQubits in 3 .. 10 {
            mutable randomInput = [];
            for i in 1 .. numQubits {
                set randomInput += [DrawRandomBool(0.5)];
            }

            let copyOutput = Exercise1(Copy, randomInput);
            AllEqualityFactB(
                copyOutput,
                randomInput,
                "Incorrect output for Copy operation"
            );

            let shiftOutput = Exercise1(LeftShiftBy1, randomInput);
            let expected = randomInput[1...] + [false];
            AllEqualityFactB(
                shiftOutput,
                expected,
                "Incorrect output for LeftShiftBy1 operation"
            );
        }
    }
}
