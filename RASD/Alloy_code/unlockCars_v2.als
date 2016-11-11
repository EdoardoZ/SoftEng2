abstract sig Person{}

sig Position{}
sig Identifier{}
sig PowerUser extends Person{
	pos: one Position,
	bookedVehicle:one LockedCar,
	unlockRequest: lone UnlockRequest,
	drivenCar: lone UnlockedCar
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

/*FACT*/

fact userBook1Car{ /*one user can book only 1 car*/
	no p,p' :PowerUser | p.bookedVehicle=p'.bookedVehicle and p!=p' 
	}

fact drivenCarEqualToBooked{/*user can drive only the booked car*/
	 all p:PowerUser | p.drivenCar.ID=p.bookedVehicle.ID
	}

fact unlockedCarEqualLockedCar{/*number of unlocked car <=locked one*/
	#UnlockedCar<=#LockedCar
	}

fact noUserDriveSameCar{/*one user can drive only one car*/
	no p,p':PowerUser | p.drivenCar= p'.drivenCar and p!=p'
	}

fact only2CarsWithSameID{
	all c,c':LockedCar | c.ID != c'.ID implies c != c'
 	all c,c':LockedCar | c.ID = c'.ID implies c = c'
 	all c,c':UnlockedCar | c.ID != c'.ID implies c != c'
 	all c,c':UnlockedCar | c.ID = c'.ID implies c = c'
	}

fact noCarsInSamePosition{/*no different cars with same position*/
	all c,c':LockedCar | c.unlockArea=c'.unlockArea implies c=c'
	all c,c':LockedCar | c.unlockArea!=c'.unlockArea implies c!=c'
	all c,c':UnlockedCar | c.unlockArea=c'.unlockArea implies c=c'
	all c,c':UnlockedCar | c.unlockArea!=c'.unlockArea implies c!=c'
	}

fact drivedCarEqualBooked{/*users can only drive car they booked*/
	all p:PowerUser | p.drivenCar.unlockArea=p.bookedVehicle.unlockArea
	}

fact noUnlock4NonBookedCar{/*one user can unlock only the car he has booked*/
	all p:PowerUser, c:LockedCar | p.unlockRequest.car=c implies p.bookedVehicle=c
	}

fact unlockCarRequireUser{/*no unlocked car without user*/
	#UnlockedCar>0 implies #PowerUser>0    
	}

fact usersThatUnlockCarHaveAnUnlockRequest{
	all c:UnlockedCar,p:PowerUser | p.unlockRequest.car.ID=c.ID
	}

fact unlockOnlyInUnlockArea{/*user can unlock a car only if he is in car's unlockArea*/
	no p:PowerUser, c:UnlockedCar | 
		(p.pos not in c.unlockArea) and p.unlockRequest.car.ID=c.ID 
	}

/*PREDICATES*/

pred unlockCar[uc:UnlockedCar, lc:LockedCar, p:PowerUser]{
	p.bookedVehicle=lc &&

	uc.ID=lc.ID &&
	uc.unlockArea=lc.unlockArea 
	}

run unlockCar

/*ASSERTS*/

assert TwoCarAreSame{/*cars with same ID and unlockArea are the same car*/
	all c,c':Car | c.ID=c'.ID implies c.unlockArea=c'.unlockArea
	}

check TwoCarAreSame

assert NoUserUnlockBookedCar{ /*users can't have an unlockRequest for a car they haven't book*/
	all c:Car, u,u':UnlockRequest ,p,p':PowerUser | (p.bookedVehicle=c and p!=p' and u'!=u) implies 
			((u.user=p and u.car=c) and not(u'.user=p' and u'.car=c)) 
	}

check NoUserUnlockBookedCar

assert NoMultipleCarWithSameID{
	no c,c':LockedCar | c'.ID=c.ID and c'!=c
	no c,c':UnlockedCar | c'.ID=c.ID and c'!=c
	}

check  NoMultipleCarWithSameID

assert UserMakeRequest{/*users have to make request for unlock cars they have book*/
	all p:PowerUser,c:UnlockedCar,u:UnlockRequest |  
		(p.pos in c.unlockArea and p=u.user and p.bookedVehicle.ID=c.ID) implies u.car.ID=c.ID 
	}

check UserMakeRequest
