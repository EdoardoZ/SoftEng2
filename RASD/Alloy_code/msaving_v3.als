/**DESCRIBE A SITUATION WHERE THE BEST SPA IS ALREADY CHOSEN**/

/**SIGNATURES**/

sig Position{}
sig Identifier{}

sig Car{
	ID:one Identifier,
	pos: one Position
	}

abstract sig Status{}
sig Full extends Status{}
sig Free extends Status{}

sig ChargingSlot{}
sig ExclusiveSlot extends ChargingSlot{
  relatedParkingArea: one SpecialParkingArea
}

sig SpecialParkingArea{
	carsNumber: one Status, /*refers to the number of exclusiveSlots*/
	area: some Position,
	slots: some ChargingSlot,
	exclusiveSlots: set ExclusiveSlot,
	}{#slots >= #exclusiveSlots
		#area=#slots}

sig Destination{
	destArea: some Position, /*area within a specific range from original destination*/
	closestArea: one SpecialParkingArea
}

/**FACT**/

fact only2CarsWithSameID{
	all c,c':Car | c.ID != c'.ID implies c != c'
 	all c,c':Car | c.ID = c'.ID implies c = c'
	}

fact noCarsInSamePosition{/*no different cars with same position*/
	all c,c':Car | c.pos=c'.pos implies c=c'
	all c,c':Car | c.pos!=c'.pos implies c!=c'
	}

fact exclusiveSlotsSubsetOfSlots{
  all spa: SpecialParkingArea, xs: ExclusiveSlot |
    (xs in spa.exclusiveSlots) implies (xs in spa.slots)
  }

fact noSlotInMultipleSpecialParkingArea{/*no 2 equal slot in different parkingArea*/
	all slot: ChargingSlot, spa1,spa2: SpecialParkingArea |
		spa1!=spa2 implies  (slot not in spa1.slots) or (slot not in spa2.slots)
	 all spa1,spa2: SpecialParkingArea, slot: ChargingSlot|
  		(slot in spa1.slots) and (slot in spa2.slots) implies spa1=spa2
  }

fact disjointParkingAreas{/*no 2 equal Special Parking Areas*/
  all spa1,spa2: SpecialParkingArea, p: Position |
  	spa1!=spa2 implies  (p not in spa1.area) or (p not in spa2.area)
 all spa1,spa2: SpecialParkingArea, p: Position |
  	(p in spa1.area) and (p in spa2.area) implies spa1=spa2
}

fact notTooDistantParkingAreas{
	all d:Destination | (d.closestArea.area & d.destArea) !=none	
	}

fact notFullSpecialParkingAreas{
	all d:Destination | d.closestArea.carsNumber=Free	
	}

fact noExclusiveSlotOutsideSpecialParkingArea{
  all xs: ExclusiveSlot, spa: SpecialParkingArea |
    xs.relatedParkingArea = spa implies xs in spa.slots
  }

fact slotsCapacityConstraint{
  #(Car.pos & SpecialParkingArea.area)
    =< #SpecialParkingArea.slots
  }

/**PREDICATES**/

pred getAlternative[dst:Destination,spa:SpecialParkingArea]{
	dst.closestArea=spa
	}

run getAlternative

/**ASSERT**/

assert ClosestAreaIsReachableAndFree{
	all d:Destination, spa:SpecialParkingArea | getAlternative[d,spa] implies ((d.destArea & spa.area)!=none and 
		spa.carsNumber=Free)
	}
check ClosestAreaIsReachableAndFree
