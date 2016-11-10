abstract sig Person{}

sig Position{}
sig Identifier{}
sig PowerUser extends Person{
	pos: one Position,
	bookedVehicle:one LockedCar,
	unlockRequest: lone UnlockRequest,
	drivedCar: lone UnlockedCar
	}


sig UnlockRequest{
	user:one PowerUser,
	car:one LockedCar
	}{#UnlockRequest <= #PowerUser}

 
abstract sig Car{
	ID:one Identifier,
	unlockArea: set Position
	}{#unlockArea>0}

sig LockedCar extends Car{}

sig UnlockedCar extends Car{}

//FACT

fact userBook1Car{//2 utenti non possono prenotare la stessa macchina
	no p,p' :PowerUser | p.bookedVehicle=p'.bookedVehicle and p!=p' 
	}

fact drivedCarEqualToBooked{//macchina guidata=macchina prenotata
	 all p:PowerUser | p.drivedCar.ID=p.bookedVehicle.ID
	}

fact unlockedCarEqualLockedCar{// #macchineSbloccate<=#macchinebloccate
	#UnlockedCar<=#LockedCar
	}

fact noUserDriveSameCar{
	no p,p':PowerUser | p.drivedCar= p'.drivedCar and p!=p'
	}

fact only2CarsWithSameID{//ptoblema 3 macchine non devono avere lo stesso ID
	all c,c':LockedCar | c.ID != c'.ID implies c != c'
 	all c,c':LockedCar | c.ID = c'.ID implies c = c'
 	all c,c':UnlockedCar | c.ID != c'.ID implies c != c'
 	all c,c':UnlockedCar | c.ID = c'.ID implies c = c'
	}

fact noCarsInSamePosition{
	all c,c':LockedCar | c.unlockArea=c'.unlockArea implies c=c'
	all c,c':LockedCar | c.unlockArea!=c'.unlockArea implies c!=c'
	all c,c':UnlockedCar | c.unlockArea=c'.unlockArea implies c=c'
	all c,c':UnlockedCar | c.unlockArea!=c'.unlockArea implies c!=c'
	}

fact drivedCarEqualBooked{
	all p:PowerUser | p.drivedCar.unlockArea=p.bookedVehicle.unlockArea
	}

fact noUnlock4NonBookedCar{
	all p:PowerUser, c:LockedCar | p.unlockRequest.car=c implies p.bookedVehicle=c
	}

fact twoCarsAreSame{
	#UnlockedCar>0 implies #PowerUser>0    
	}

fact usersThatUnlockCarHaveAUnlockRequest{
	all c:UnlockedCar,p:PowerUser | p.unlockRequest.car.ID=c.ID
	}

fact unlockOnlyInUnlockArea{
	no p:PowerUser, c:UnlockedCar | 
		(p.pos not in c.unlockArea) and p.unlockRequest.car.ID=c.ID 
	}

//PREDICATES

pred unlockCar[uc:UnlockedCar, lc:LockedCar, p:PowerUser]{
	p.bookedVehicle=lc &&

	uc.ID=lc.ID &&
	uc.unlockArea=lc.unlockArea 
	}

run unlockCar

//ASSERTS

//2 macchine con lo stesso id sono uguali
assert TwoCarAreSame{
	all c,c':Car | c.ID=c'.ID implies c.unlockArea=c'.unlockArea
	}

check TwoCarAreSame

// non c'è un altro utente che sblocca una macchina prenotata
assert NoUserUnlockBookedCar{ 
	all c:Car, u,u':UnlockRequest ,p,p':PowerUser | (p.bookedVehicle=c and p!=p' and u'!=u) implies ((u.user=p and u.car=c) and 
		not(u'.user=p' and u'.car=c)) 
	}

check NoUserUnlockBookedCar

assert NoMultipleCarWithSameID{// non ci sono 2 macchine con lo stesso ID
	no c,c':LockedCar | c'.ID=c.ID and c'!=c
	no c,c':UnlockedCar | c'.ID=c.ID and c'!=c
	}

check  NoMultipleCarWithSameID

//un utente fa richiesta per sbloccare la macchina
assert UserMakeRequest{
	all p:PowerUser,c:UnlockedCar,u:UnlockRequest |  
		(p.pos in c.unlockArea and p=u.user and p.bookedVehicle.ID=c.ID) implies u.car.ID=c.ID 
	}

check UserMakeRequest

