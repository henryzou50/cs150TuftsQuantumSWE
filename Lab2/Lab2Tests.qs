// QSD Lab 2 Tests
// Copyright 2023 The MITRE Corporation. All Rights Reserved.
//
// DO NOT MODIFY THIS FILE.

namespace Lab2 {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Random;

    @Test("QuantumSimulator")
    operation Exercise1Test () : Unit {
        for numQubits in 3 .. 10 {
            use qubits = Qubit[numQubits];

            Exercise1(qubits);

            for index in 0 .. numQubits - 1 {
                Ry(PI() * IntAsDouble(index) / -12.0, qubits[index]);
            }

            AssertAllZero(qubits);
        }
    }


    @Test("QuantumSimulator")
    operation Exercise2Test () : Unit {
        for i in 0 .. 4 {
            mutable states = [];
            use qubits = Qubit[5];
            for j in 0 .. 4 {
                set states += [DrawRandomInt(0, 1)];
                if states[j] == 1 {
                    X(qubits[j]);
                }
            }

            let results = Exercise2(qubits);

            AllEqualityFactI(states, results, "Exercise 2 test failed.");
            ResetAll(qubits);
        }
    }


    @Test("QuantumSimulator")
    operation Exercise3Test () : Unit {
        for numQubits in 1 .. 8 {
            use qubits = Qubit[numQubits];

            Exercise3(qubits);

            ApplyToEach(H, qubits);

            AssertAllZero(qubits);
        }
    }


    @Test("QuantumSimulator")
    operation Exercise4Test () : Unit {
        for numQubits in 1 .. 8 {
            use qubits = Qubit[numQubits];

            ApplyToEach(H, qubits);

            Exercise4(qubits);

            Z(qubits[numQubits - 1]);
            ApplyToEach(H, qubits);

            AssertAllZero(qubits);
        }
    }
}