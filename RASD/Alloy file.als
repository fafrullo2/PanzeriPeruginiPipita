
abstract sig Boolean{}

sig True extends Boolean{}

sig False extends Boolean{}

sig Photo{}

sig CF{}

sig Person{
    cf: one CF
}

sig Plate{}

sig Vehicle {
	ownedby: one Person,
    plate: one Plate
}

sig User{}

sig GPScoord{
	latitude: one Int,
	longitude: one Int
}

sig GPSline{
	start: one GPScoord,
    end: one GPScoord
}{start!=end}

sig Perimeter {
    first: one GPSline,
    last: one GPSline,
    side: some GPSline
}{#side>0  }

sig Area {
    perimeter: one Perimeter,
	segnalationsInside: some Segnalation,
	dangerLevel: one Int
}

sig Violation {
	coords: one GPScoord,
	time: one Int,
}{time>=0 and time<7
}

abstract sig ViolationType{}

sig ExpiredTicket extends ViolationType{}

sig UnauthorizedParking extends ViolationType{}

sig Segnalation {
	maker: one User,
	vehicle: one Vehicle,
    violation: one Violation,
    violationType: ViolationType,
	photo: one Photo,
    takenCareOf: one Boolean,
    writtenPlate: one Plate
}

fun getCoords[s:Segnalation]: GPScoord{
    s.violation.coords
}

fun getTime[s:Segnalation]: Int{
    s.violation.time
}

abstract sig Authority {
    person: one Person
}

sig MunicipalAuthority extends Authority{}

sig Policeman extends Authority{}

sig Ticket{
    segnalations: one Segnalation,
    policeman: one Policeman,
    issuedTo: one Person
}{#segnalations>0}


//======================================================================================
//facts and functions
//======================================================================================


fact booleanValues{
    #True=1 and #False=1 and #Boolean=2 and 
    (all b: Boolean |b = True or b = False) and 
    (no b: Boolean | b in True and b in False) 
}

fact uniquePhoto{
    all  p1: Photo | no disj s1, s2 : Segnalation | s1.photo=p1 and s2.photo=p1  
}

fact noLonePhoto{
    all p1:Photo | p1 in Segnalation.photo
}


fact noSameCF{
    no disj p1, p2: Person | p1.cf=p2.cf
}

fact noSamePlate{
    no disj vei1, vei2: Vehicle | vei1.plate=vei2.plate
}

fact noDoubleJob{
    no a: Authority | a in MunicipalAuthority and a in Policeman
}

fact cityLimits{
    all gps: GPScoord | gps.latitude>0 and gps.longitude>0 and gps.latitude<7 and gps.longitude<7
}

fact noDoubleCoordinates{
    all c1: GPScoord | no c2: GPScoord | c1 != c2 and c1.longitude=c2.longitude and c1.latitude= c2.latitude
}

fact noDOubleLines{
    all l1, l2: GPSline | l1=l2 iff((l1.start=l2.start and l1.end=l2.end)or(l1.start=l2.end and l1.end=l2.start))
}


fact perimeterProperties{
    (all p:Perimeter| p.first.start=p.last.end) 
    and 
    (all p:Perimeter| some l1:GPSline | 
    l1 in p.side and p.first.end=l1.start)
    and 
    (all p: Perimeter | some l2: GPSline |
    l2 in p.side and p.last.start=l2.end) 
    and
    (all p:Perimeter| no l1: GPSline | p.first=l1 and l1 in p.side)
    and
    (all p:Perimeter| no l1: GPSline | p.last=l1 and l1 in p.side)
}

fact areaProperties{
    all a: Area| #a.segnalationsInside>=0 and a.dangerLevel=#a.segnalationsInside
}

fact noMissmatchingPlates{
    all s: Segnalation| s.vehicle.plate=s.writtenPlate
}

fact allPlates{
    #Segnalation.writtenPlate=#Vehicle
}

fact violationTypeCardinality{
    #ViolationType=2 and #ExpiredTicket=1 and #UnauthorizedParking=1
}

fact allSegnalationsInAnArea{
    all s: Segnalation | s in Area.segnalationsInside
}

fact eitherAllTakenCareOrNone{
    all s1, s2: Segnalation | (getCoords[s1]=getCoords[s2] and getTime[s1]=getTime[s2] and s1.writtenPlate=s2.writtenPlate and s1.violationType=s2.violationType) implies (s1.takenCareOf=s2.takenCareOf)
}



fact allTakenCareOf{


}

fact sameVehicle{
    all disj s1, s2 : Segnalation | all t: Ticket |
    (s1 in t.segnalations and s2 in t.segnalations) implies s1.vehicle=s2.vehicle

}

fact takenCareOfRule{
    all s: Segnalation |
    s in Ticket.segnalations iff s.takenCareOf=True
}
fact rightPersonBilled{
    all t: Ticket| t.issuedTo=t.segnalations.vehicle.ownedby
}

fact noDoubleBilling{
    all t1: Ticket| all s: Segnalation|
    s in t1.segnalations implies no t2:Ticket| t2 != t1 and s in t2.segnalations
}


//=====================================================
//assertions
//=====================================================

//G1
assert eachSegnalationHasOneAndOnlyPhoto{
    all disj s1, s2: Segnalation| 
    #s1.photo=1 and #s2.photo=1 and s1.photo != s2.photo
    and #Photo=#Segnalation
}

//G3
assert everySegnalationHasOneAndOnlyPlate{
    all disj s1, s2: Segnalation|
    s1.writtenPlate=s2.writtenPlate iff s1.vehicle=s2.vehicle
}

//G4
assert everySegnalationHasTimeAndPlace{
    all s1: Segnalation | 
    #s1.violation=1 and #s1.violation.coords=1 and #s1.violation.time=1 and #s1.violation.coords.latitude=1 and #s1.violation.coords.longitude=1
}

//G2.4
assert ticketToVehicleOwner{
    all v:Vehicle | all s: Segnalation | all t: Ticket|
    (s in t.segnalations and v = s.vehicle) implies t.issuedTo=v.ownedby
}

check eachSegnalationHasOneAndOnlyPhoto for 6
check everySegnalationHasOneAndOnlyPlate for 6
check everySegnalationHasTimeAndPlace for 6
check ticketToVehicleOwner for 6
pred world1{
    #Vehicle=3
    #Segnalation=3
    #Ticket=2
    #Violation=2
    #Person>2

    

}

run world1 for 10