------------------------------ MODULE SecSpec ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS PassMgrMasterPwd, EmailPwd, iPhonePin
VARIABLES stolen
Locations == {"Memory", "MBP", "LastPass", "iPhone"}
Passwrds == {PassMgrMasterPwd, EmailPwd, iPhonePin, "Ledger Pin", "MBP Pwd"}
Devices == {"iPhone", "UnlockediPhone", "Ledger", "MBP"}
Pwd == [PassMgrMasterPwd |-> "Memory", EmailPwd |-> "LastPass"]
TypeInv == stolen \in [devices : SUBSET Devices, passwds : SUBSET Passwrds]

Init == TypeInv /\ stolen = [devices |-> {}, passwds |-> {}]

Knows(a, c) == a \in c.passwds
Has(a, c) == a \in c.devices


UnlockedMBP(c) == /\ Has("MBP", c)
                  /\ \/ Knows("MBP Pwd", c)
                     \/ Knows("MBP Recovery Code", c)

UnlockedPhone(c) == \/ Has("UnlockediPhone", c)
                    \/ Has("iPhone", c) /\ Knows(iPhonePin, c)

AuthyCode(c) == \/ UnlockedPhone(c) /\ Knows("AuthyPin", c)
                \/ UnlockedMBP(c) /\ Knows("AuthyPwd", c)
                \/ Knows("AuthyMasterPwd", c)

ReadEmailAccess(c) == \/ Knows(EmailPwd, c) /\ AuthyCode(c)
                      \/ UnlockedPhone(c)

ReadEmail == ReadEmailAccess(stolen)
StealEmail(c) == \/ Knows(EmailPwd, c) /\ AuthyCode(c)



StealAnyPassword == stolen' = [stolen EXCEPT !.passwds = @ \union {CHOOSE p \in Passwrds : p \notin @}]
StealPhone == stolen' = [stolen EXCEPT !.devices = @ \union {"iPhone"}]
StealPhonePin == stolen' = [stolen EXCEPT !.passwds = @ \union {iPhonePin}]
Attack ==
          \/ StealPhone
          \/ StealAnyPassword

Next == Cardinality(stolen.devices) < 2 /\ Attack
Spec == Init /\ [][Next]_stolen

EmailNeverStolen == [](~ StealEmail(stolen))
CanRestoreInfoIfAllDevicesAreStolen == TRUE

=============================================================================
\* THEOREM Spec => []EmailNeverStolen
