# Recovering Single-Crossing Preferences From Approval Ballots

To compile the code, use the following command:

``g++ -std=c++11 -O2 exhaust_proof.cpp -o exhaust_proof``

To run the check required in the proof of Lemma 32, invoke the compiled program as:

``echo "1" | ./exhaust_proof``

To run the check required in the proof of Lemma 33, invoke the compiled program as:

``echo "2" | ./exhaust_proof``
