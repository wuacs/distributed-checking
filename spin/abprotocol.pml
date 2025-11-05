mtype = { F0, F1, ACK }
chan ch12 = [1] of { mtype, byte };   /* data: (F0/F1, payload) */
chan ch21 = [1] of { mtype, byte };   /* acks: (ACK, bit)       */
chan sap1 = [0] of { byte };
chan sap2 = [0] of { byte };

/* Sender */
proctype Tx(chan sap; chan cout; chan cin) {
    bit nexttosend = 0;
    byte mess;
    do
    :: sap?mess ->
        do
        :: cout! (nexttosend==0->F0:F1), mess;   /* send data with bit */
           /* wait for matching ACK (with same bit) or keep retrying */
           if
           :: cin?ACK, nexttosend -> break       /* good ACK matches bit */
           :: skip                               /* model “no progress” (timeout / keep sending) */
           fi
        od;
        nexttosend = 1 - nexttosend
    od
}

/* Receiver */
proctype Rx(chan sap; chan cout; chan cin) {
    bit expected = 0;
    bit seqn;
    byte mess;
    do
    :: cin? (seqn==0->F0:F1), mess ->
        if
        :: seqn == expected ->
             sap!mess;                       /* deliver once */
             cout!ACK, expected;             /* ACK the just-accepted bit */
             expected = 1 - expected
        :: else ->
             /* duplicate: do NOT deliver, but repeat last ACK
                (which is 1 - expected, the last accepted bit) */
             cout!ACK, (1 - expected)
        fi
    od
}

/* Loss model: non-deterministically eats messages */
proctype Error(chan c) {
    do :: c?_,_ od
}

init {
  atomic {
    run Tx(sap1, ch12, ch21);
    run Rx(sap2, ch21, ch12);
    run Error(ch12);
    run Error(ch21);
  }
}
