
sig Boolean{}

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
    side: set GPSline
}{#side>0}

sig Area {
    perimeter: one Perimeter,
	segnalations: some Segnalation,
	dangerLevel: one Int
}

sig Violation {
	coords: one GPScoord,
	time: one Int,
}{time>=0 and time<7
}

sig ViolationType{}

sig ExpiredTicket extends ViolationType{}

sig UnauthorizedParking extends ViolationType{}

sig Segnalation {
	maker: one User,
	vehicle: one Vehicle,
    violation: one Violation,
    violationType: ViolationType,
	photo: one Photo,
    takenCareOf: one Boolean
}

abstract sig Authority {
    person: Person
}

sig MunicipalAuthority extends Authority{}

sig Policeman extends Authority{}

sig Ticket{
    filing:  Segnalation -> one Policeman
}

//TODO infraction->violation
//======================================================================================
//facts and functions
//======================================================================================


fact booleanValues{
    #True=1 and #False=1 and 
    (all b: Boolean |b in True or b in False) and 
    (no b: Boolean | b in True and b in False) 
}

fact noSameCF{
    no disj p1, p2: Person | p1.cf=p2.cf
}

fact noSamePlate{
    no disj vei1, vei2: Vehicle | vei1.plate=vei2.plate
}

fact cityLimits{
    all gps: GPScoord | gps.latitude>0 and gps.longitude>0 and gps.latitude<7 and gps.longitude<7
}


fact perimeterProperties{
    (all p:Perimeter| p.first.start=p.last.end) 
    and 
    (all p:Perimeter| some l1:GPSline | 
    l1 in p.side and p.first.end=l1.start)
    and 
    (all p: Perimeter | some l2: GPSline |
    l2 in p.side and p.last.start=l2.end) 
}

fact areaProperties{
    all a: Area| #a.segnalations>=0 and a.dangerLevel=#a.segnalations
}

fact discardSegnalationsAlreadyTakenCareOf{
    all s1: Segnalation | no s2: Segnalation | s2 != s1 and (s1.takenCareOf in True) and
                            s1.vehicle.plate = s2.vehicle.plate 
                            and s1.violation.coords.longitude-s2.violation.coords.longitude<1 and s1.violation.coords.longitude-s2.violation.coords.longitude>-1
                            and s1.violation.coords.latitude-s2.violation.coords.latitude<1 and s1.violation.coords.latitude-s2.violation.coords.latitude>-1 and
                            s1.violation.time-s2.violation.time<2 and s1.violation.time-s2.violation.time>-2
                            and s1.violationType=s2.violationType
}

fact ticketWritten{
    (all s1: Segnalation| s1.takenCareOf=True iff s1 in (Ticket.filing).Policeman)
    and 
    (all disj s1, s2: Segnalation| s1.takenCareOf=True /**/ )
}

