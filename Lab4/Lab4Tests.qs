// QSD Lab 4 Tests
// Copyright 2023 The MITRE Corporation. All Rights Reserved.
//
// DO NOT MODIFY THIS FILE.

namespace Lab4 {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Intrinsic;

    @Test("QuantumSimulator")
    operation Exercise1Test () : Unit {
        let buffers = [
            [false, false],
            [false, true],
            [true, false],
            [true, true]
        ];

        for i in 1 .. 10 {
            for buffer in buffers {
                use qubits = Qubit[2];
                H(qubits[0]);
                CNOT(qubits[0], qubits[1]);

                Exercise1(buffer, qubits[0]);

                CNOT(qubits[0], qubits[1]);
                H(qubits[0]);

                EqualityFactB(
                    ResultAsBool(M(qubits[0])),
                    buffer[0],
                    "First qubit is incorrect."
                );
                EqualityFactB(
                    ResultAsBool(M(qubits[1])),
                    buffer[1],
                    "Second qubit is incorrect."
                );

                ResetAll(qubits);
            }
        }
    }


    @Test("QuantumSimulator")
    operation Exercise2Test () : Unit {
        let buffers = [
            [false, false],
            [false, true],
            [true, false],
            [true, true]
        ];

        for i in 1 .. 10 {
            for buffer in buffers {
                use qubits = Qubit[2];
                H(qubits[0]);
                CNOT(qubits[0], qubits[1]);
                if buffer[1] {
                    X(qubits[0]);
                }
                if buffer[0] {
                    Z(qubits[0]);
                }

                let result = Exercise2(qubits[0], qubits[1]);

                AllEqualityFactB(
                    result,
                    buffer,
                    "Exercise 2 result is incorrect."
                );

                ResetAll(qubits);
            }
        }
    }


    @Test("QuantumSimulator")
    operation Exercise3Test () : Unit {
        for i in 0 .. 7 {
            let aPublic = (i / 4 == 1);
            let aSecret = (i / 2 % 2 == 1);
            let bPublic = (i % 2 == 1);
            use qubit = Qubit();
            let result = Exercise3(aPublic, aSecret, bPublic, qubit);

            if aPublic { H(qubit); }
            if aSecret { X(qubit); }

            EqualityFactB(
                result,
                (aPublic == bPublic),
                $"Keep/reject value is incorrect."
            );

            AssertAllZero([qubit]);
        }
    }


    @Test("QuantumSimulator")
    operation Exercise4Test () : Unit {
        for i in 0 .. 7 {
            let aPublic = (i / 4 == 1);
            let aSecret = (i / 2 % 2 == 1);
            let bPublic = (i % 2 == 1);
            use qubit = Qubit();
            if aSecret { X(qubit); }
            if aPublic { H(qubit); }

            let (bSecret, keep) = Exercise4(aPublic, bPublic, qubit);

            EqualityFactB(
                keep,
                (aPublic == bPublic),
                "Keep/reject value is incorrect."
            );

            if (keep) {
                EqualityFactB(
                    aSecret,
                    bSecret,
                    "Secret bits do not match."
                );
            }

            Reset(qubit);
        }
    }
}