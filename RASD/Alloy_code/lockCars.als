/**DESCRIBE A SITUATION WHERE CAR IS NOT MOVING**/

/**SIGNATURES**/

abstract sig Person{}

abstract sig Engine{}
sig ON extends Engine {}
sig OFF extends Engine{}

abstract sig LockingTime{}
sig Ended extends LockingTime{}
sig Running extends LockingTime{}

sig Position{}
sig Identifier{}

sig Parking{
	pos:one Position
	}

sig Passenger extends Person{}
sig Driver extends Person{}

abstract sig Car{
	ID:one Identifier,
	pos: one Position,
	passengers:set Passenger,
	driver: lone Driver,
	engine: one Engine,
	timer: lone LockingTime
	}{#passengers <4}

sig LockedCar extends Car{}
sig UnlockedCar extends Car{}{#driver=1}

/**FACT**/

fact only2CarsWithSameID{
	all c,c':LockedCar | c.ID != c'.ID implies c != c' 
 	all c,c':LockedCar | c.ID = c'.ID implies c = c'
 	all c,c':UnlockedCar | c.ID != c'.ID implies c != c'

 /*no 3 cars with same id*/
 	all c,c',c'':UnlockedCar | (c.ID = c'.ID and c.ID=c''.ID) implies 
		((c = c' and c.engine=c'.engine) or (c=c'' and c.engine=c''.engine) or (c'=c'' and c'.engine=c''.engine))
	}

fact noDifferentCarsInSamePosition{
	all c,c':LockedCar | c.pos=c'.pos implies c=c'
	all c,c':LockedCar | c.pos!=c'.pos implies c!=c'
	all c,c':UnlockedCar | c.pos!=c'.pos implies c!=c' 

 /*no 3 cars with same position*/
	all c,c',c'':UnlockedCar | (c.pos = c'.pos and c.pos=c''.pos) implies 
		((c = c' and c.engine=c'.engine) or (c=c'' and c.engine=c''.engine) or (c'=c'' and c'.engine=c''.engine))
	}

fact onlyOneDriverPerCar{/*2 user can't drive the same car */
	all c,c':UnlockedCar | (c.engine=ON and c'.engine=OFF and c.ID=c'.ID) implies c.driver=c'.driver
	all c,c':UnlockedCar | c.ID!=c'.ID implies c.driver!=c'.driver
	}

fact noUnlockTimeIfEngineOn{/*timer start only when engine is turned off*/
	all c:UnlockedCar | c.engine=ON implies #c.timer=0 and #c.driver=1
	}

fact timerIfEngineIsStopped{/*if engine is OFF there'is a timer + if engine OFF car is parked*/ 
	all c:UnlockedCar | c.engine=OFF implies c.timer=Running 
	all c:UnlockedCar | c.engine=OFF implies ( c.pos in Parking.pos)
	}

fact oneParkingForPosition{
	all p,p':Parking | p.pos=p'.pos implies p=p'
	all p,p':Parking | p.pos!=p'.pos implies p!=p'
	} 

fact noSamePassengersOnDifferentCars{
	all c,c':UnlockedCar | c.ID!=c'.ID implies ((c.passengers & c'.passengers)=none)
	}


/*locked cars fact*/

fact carsLockedOnlyWithEngineOff{
	all c:LockedCar | c.engine=OFF
	}

fact carsLockedIsInAParking{
	all c:LockedCar | c.pos in Parking.pos
	}

fact carsLockedHasNoPersonOnBoard{
	all c:LockedCar | #c.passengers=0 and #c.driver=0 
	}

fact noCarsLockedIfShortTimeIsPasses{/*all lockedCars unlock after a given time*/
	all c:LockedCar | c.timer=Ended
	}

fact lockedCarRequiresOneUnlockedCar{
	all uc:UnlockedCar, lc:LockedCar | uc.ID=lc.ID implies uc.pos=lc.pos
	}

/**PREDICATES**/

pred turnOff[c,c':UnlockedCar]{
	c.engine=ON &&

	c'.engine=OFF &&
	c'.ID=c.ID &&
	c'.pos=c.pos	
	}

pred lockCar[lc:LockedCar, uc:UnlockedCar]{
	uc.engine=OFF &&

	lc.ID=uc.ID &&
	lc.pos=uc.pos 
}

pred show [lc:LockedCar ,uc,uc':UnlockedCar]{
	turnOff[uc,uc']
	lockCar[lc,uc']
	}

run turnOff 
run lockCar
run show

/**ASSERT**/

assert UnlockedCarIsTheLockedOne{/*check if locked and unlocked cars are the same*/
	all uc,uc':UnlockedCar ,lc:LockedCar | 
		turnOff[uc,uc'] and lockCar[lc,uc'] implies 	
			(uc.ID=lc.ID and uc.pos=lc.pos)
	}
check UnlockedCarIsTheLockedOne

assert LockedCarStatus{/*check if the status of LockedCar is correct*/
	all uc:UnlockedCar, lc:LockedCar | lockCar[lc,uc] implies lc.ID=uc.ID and lc.pos in Parking.pos and 
		lc.engine=OFF and #lc.driver=0 and #lc.passengers=0 and lc.timer=Ended and lc.pos=uc.pos	
	}
check LockedCarStatus

assert UnlockedCarWithEngineOffStatus{/*check if the status of UnlockedCar with engine turned off is correct*/
	all uc,uc':UnlockedCar | turnOff[uc,uc'] implies (uc.driver=uc'.driver and 
		uc.pos=uc'.pos and uc.engine!=uc'.engine and uc.ID=uc'.ID and uc'.timer=Running and #uc.timer=0)
	}
check UnlockedCarWithEngineOffStatus
