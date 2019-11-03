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

sig User{
    person: one Person,
    areaOfInterest: some Area
}

sig GPScoord{
	latitude: one Int,
	longitude: one Int
}


sig Intervention{}

sig Area {
	segnalationsInside: some Segnalation,
	dangerLevel: one Int,
    interventions: some Intervention
}

sig PositionAndTime {
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
    positionAndTime: one PositionAndTime,
    violationType: ViolationType,
	photo: one Photo,
    takenCareOf: one Boolean,
    writtenPlate: one Plate
}

fun getCoords[s:Segnalation]: GPScoord{
    s.positionAndTime.coords
}

fun getTime[s:Segnalation]: Int{
    s.positionAndTime.time
}

abstract sig Authority {
    person: one Person
}

sig MunicipalAuthority extends Authority{
    trackedUsers: some User,
    trackedAreas: some Area,
    trackedVehicles: some Vehicle
}

sig Policeman extends Authority{}

sig Ticket{
    segnalations: one Segnalation,
    policeman: one Policeman,
    issuedTo: one Person
}{#segnalations>0}


//======================================================================================
//facts
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
    no p: Person| p in MunicipalAuthority.person and p in Policeman.person
    no disj p1, p2:Policeman | p1.person=p2.person
    no disj ma1, ma2: MunicipalAuthority| ma1.person=ma2.person
    no disj u1, u2: User| u1.person=u2.person
}

fact cityLimits{
    all gps: GPScoord | gps.latitude>0 and gps.longitude>0 and gps.latitude<7 and gps.longitude<7
}

fact noDoubleCoordinates{
    all c1: GPScoord | no c2: GPScoord | c1 != c2 and c1.longitude=c2.longitude and c1.latitude= c2.latitude
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
//G2
assert dataMining{
    all u: User| all ma: MunicipalAuthority|
    #u.areaOfInterest>=0 and #ma.trackedAreas>=0 and #ma.trackedUsers>=0 and #ma.trackedVehicles>=0
}
//G3
assert everySegnalationHasOneAndOnlyPlate{
    all disj s1, s2: Segnalation|
    s1.writtenPlate=s2.writtenPlate iff s1.vehicle=s2.vehicle
}

//G4
assert everySegnalationHasTimeAndPlace{
    all s1: Segnalation | 
    #s1.positionAndTime=1 and #s1.positionAndTime.coords=1 and #s1.positionAndTime.time=1 and #s1.positionAndTime.coords.latitude=1 and #s1.positionAndTime.coords.longitude=1
}
//GA1.2
assert interventionsSuggested{
    all a: Area| #a.interventions>=0
}
//GA2.4
assert ticketToVehicleOwner{
    all v:Vehicle | all s: Segnalation | all t: Ticket|
    (s in t.segnalations and v = s.vehicle) implies t.issuedTo=v.ownedby
}






pred world1{
    #Vehicle=2
    #Segnalation=3
    #Ticket>0
    #PositionAndTime>3
    #Person>2
    #Policeman>0
    #Area>0
    #MunicipalAuthority>0
    #User>2
    
}

run world1 for 6
check eachSegnalationHasOneAndOnlyPhoto for 6
check dataMining for 6
check everySegnalationHasOneAndOnlyPlate for 6
check everySegnalationHasTimeAndPlace for 6
check interventionsSuggested for 6
check ticketToVehicleOwner for 6