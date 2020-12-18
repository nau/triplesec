------------------------------ MODULE SecSpec ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS PassMgrMasterPwd, EmailPwd, iPhonePin
VARIABLES stolen
Locations == {"Memory", "MBP", "LastPass", "iPhone"}
Passwrds == {PassMgrMasterPwd, EmailPwd, iPhonePin}
Devices == {"iPhone", "UnlockediPhone"}
Pwd == [PassMgrMasterPwd |-> "Memory", EmailPwd |-> "LastPass"]
Init == stolen = {}

UnlockedPhone(c) == "UnlockediPhone" \in c \/ {"iPhone", iPhonePin} \subseteq c

ReadEmailAccess(c) == EmailPwd \in c \/ UnlockedPhone(c)
ReadEmail == ReadEmailAccess(stolen)

StealAnyPassword == stolen' = stolen \union CHOOSE  p \in Passwrds : p
StealPhone == stolen' = stolen \union {"iPhone"}
StealPhonePin == stolen' = stolen \union {"iPhonePin"}
Attack == Cardinality(stolen) < 2 /\ (StealPhonePin \/ StealPhone)\* \/ StealAnyPassword

Next == Attack
Spec == Init /\ [][Next]_stolen

EmailNeverStolen == [](~ ReadEmail)

=============================================================================
\* THEOREM Spec => []EmailNeverStolen
