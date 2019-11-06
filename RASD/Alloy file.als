abstract sig Boolean{}

sig True extends Boolean{}

sig False extends Boolean{}

sig Photo{}

sig SSN{}

sig Person{
    ssn: one SSN
}

sig Plate{}

sig Vehicle {
	ownedby: lone Person,
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
	reportsInside: set Report,
	dangerLevel: one Int,
    interventions: set Intervention
}{#interventions>0 implies #reportsInside>0}

sig PositionAndTime {
	coords: one GPScoord,
	time: one Int,
}{time>=0 and time<7
}

abstract sig ViolationType{}

sig ExpiredTicket extends ViolationType{}

sig UnauthorizedParking extends ViolationType{}

sig Violation{
    vehicle: one Vehicle,  //contains the plate recognised from the photo
    positionAndTime: one PositionAndTime,
    violationType: one ViolationType,
    photo: one Photo,
    writtenPlate: one Plate //plate input from user
}

sig Report {
	maker: one User,
	takenCareOf: one Boolean,
    violation: one Violation,
    dispatchedOfficer: lone Policeman
}

fun getCoords[s:Report]: GPScoord{
    s.violation.positionAndTime.coords
}

fun getTime[s:Report]: Int{
    s.violation.positionAndTime.time
}

abstract sig Authority {
    person: one Person
}

sig MunicipalAuthority extends Authority{
    trackedUsers: set User,
    trackedAreas: set Area,
    trackedVehicles: set Vehicle
}

sig Policeman extends Authority{}

sig Ticket{
    report: one Report,
    policeman: one Policeman,
    issuedTo: one Person
}


//======================================================================================
//facts
//======================================================================================

//definition of boolean true and false
fact booleanValues{
    #True=1 and #False=1 and #Boolean=2 and 
    (all b: Boolean |b = True or b = False) and 
    (no b: Boolean | b in True and b in False) 
}

//there are not 2 segnalations with the same photo
fact uniquePhoto{
    no disj s1, s2 : Violation | s1.photo=s2.photo  
}
//all the photos are part of segnalations
fact noLonePhoto{
    all p1:Photo | p1 in Violation.photo
}

fact noSameSSN{
    no disj p1, p2: Person | p1.ssn=p2.ssn
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
    all a: Area| #a.reportsInside>=0 and a.dangerLevel=#a.reportsInside
}

fact noMissmatchingPlates{
    all v: Violation| v.vehicle.plate=v.writtenPlate
}

fact allPlates{
    #Violation.writtenPlate=#Vehicle
}

fact violationTypeCardinality{
    #ViolationType=2 and #ExpiredTicket=1 and #UnauthorizedParking=1
}

fact noViolationWithSamePhoto{
    no disj v1, v2: Violation| v1.photo=v2.photo
}

fact noReportsDuplicate{
    all disj r1, r2: Report| r1.violation!=r2.violation
}

fact allSegnalationsInAnArea{
    all s: Report | s in Area.reportsInside
}
//Note that in reality it would be segnalations within a certain range of coordinates and time of the first one; but for analysis 
//simplicity I have chosen to use equality 
fact eitherAllTakenCareOrNone{
    all disj s1, s2: Report | (getCoords[s1]=getCoords[s2] and getTime[s1]=getTime[s2] and s1.violation.writtenPlate=s2.violation.writtenPlate 
    and s1.violation.violationType=s2.violation.violationType) implies (s1.takenCareOf=s2.takenCareOf and s1.dispatchedOfficer=s2.dispatchedOfficer and
    all t1: Ticket| s1 in t1.report implies no t2: Ticket| s2 in t2.report)
}


fact sameVehicle{
    all disj s1, s2 : Report | all t: Ticket |
    (s1 in t.report and s2 in t.report) implies s1.violation.vehicle=s2.violation.vehicle

}

fact takenCareOfRule{
    all s: Report |
    s in Ticket.report implies s.takenCareOf=True
}
fact rightPersonBilled{
    all t: Ticket| t.issuedTo=t.report.violation.vehicle.ownedby
}

fact noDoubleBilling{
    all disj t1, t2: Ticket| t1.report!=t2.report
}

fact dispatchedOfficerWritesTheTicket{
    all t: Ticket|
    t.policeman=t.report.dispatchedOfficer
}

fact ifTakenCareThenOfficerDispatched{
    all r: Report|
    r.takenCareOf = True implies #r.dispatchedOfficer=1
}

fact noMunicipalDBNoTickets{
    #Ticket>0 implies all v: Vehicle| #v.ownedby=1
}


//=====================================================
//assertions
//=====================================================

//G1
assert eachSegnalationHasOneAndOnlyPhoto{
    all disj s1, s2: Violation| 
    #s1.photo=1 and #s2.photo=1 and s1.photo != s2.photo
    and #Photo=#Violation
}
//G2
assert dataMining{
    all u: User| all ma: MunicipalAuthority|
    #u.areaOfInterest>=0 and #ma.trackedAreas>=0 and #ma.trackedUsers>=0 and #ma.trackedVehicles>=0
}
//G3
assert everySegnalationHasOneAndOnlyPlate{
    all disj s1, s2: Violation|
    s1.writtenPlate=s2.writtenPlate iff s1.vehicle=s2.vehicle
}

//G4
assert everySegnalationHasTimeAndPlace{
    all s1: Violation | 
    #s1.positionAndTime=1 and #s1.positionAndTime.coords=1 and #s1.positionAndTime.time=1 and 
    #s1.positionAndTime.coords.latitude=1 and #s1.positionAndTime.coords.longitude=1
}
//GA1.2
assert interventionsSuggested{
    all a: Area| #a.interventions>=0
}
//GA2.4
assert ticketToVehicleOwner{
    all v:Vehicle | all s: Report | all t: Ticket|
    (s in t.report and v = s.violation.vehicle) implies t.issuedTo=v.ownedby
}







pred world1{
    #Vehicle=2
    #Report=2
    #Ticket=1
    #Violation=3
    #Policeman=1
    #User=1
    #MunicipalAuthority=1
    #Person=3
    #Area=1

    no p: Person| p in Policeman.person and p in User.person
    
}

run world1 for 6
check eachSegnalationHasOneAndOnlyPhoto for 6
check dataMining for 6
check everySegnalationHasOneAndOnlyPlate for 6
check everySegnalationHasTimeAndPlace for 6
check interventionsSuggested for 6
check ticketToVehicleOwner for 6