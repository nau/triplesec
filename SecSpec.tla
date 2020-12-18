------------------------------ MODULE SecSpec ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS PassMgrMasterPwd, EmailPwd, iPhonePin
VARIABLES stolen
Locations == {"Memory", "MBP", "LastPass", "iPhone"}
Passwrds == {PassMgrMasterPwd, EmailPwd, iPhonePin}
Devices == {"iPhone", "UnlockediPhone"}
Pwd == [PassMgrMasterPwd |-> "Memory", EmailPwd |-> "LastPass"]
TypeInv == stolen \in [devices : SUBSET Devices, passwds : SUBSET Passwrds]

Init == TypeInv /\ stolen = [devices |-> {}, passwds |-> {}]

UnlockedPhone(c) == \/ "UnlockediPhone" \in c.devices
                    \/ "iPhone" \in c.devices /\ iPhonePin \in c.passwds

ReadEmailAccess(c) == \/ EmailPwd \in c.passwds
                      \/ UnlockedPhone(c)
ReadEmail == ReadEmailAccess(stolen)

StealAnyPassword == stolen' = [devices |-> stolen.devices, passwds |-> stolen.passwds \union CHOOSE  p \in Passwrds : p]
StealPhone == stolen' = [stolen EXCEPT !.devices = @ \union {"iPhone"}]
StealPhonePin == stolen' = [stolen EXCEPT !.passwds = @ \union {iPhonePin}]
Attack == StealPhonePin \/ StealPhone\* \/ StealAnyPassword

Next == Cardinality(stolen.devices) < 2 /\ Attack
Spec == Init /\ [][Next]_stolen

EmailNeverStolen == [](~ ReadEmail)

=============================================================================
\* THEOREM Spec => []EmailNeverStolen
