
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
} {//time misured in seconds, 86400 seconds in one day, refreshed each week
	time>=0 and time<7
}

sig ExpiredTicket extends Violation{}

sig UnauthorizedParking extends Violation{}

sig Segnalation {
	maker: one User,
	vehicle: one Vehicle,
    infraction: one Violation,
	photo: one Photo,
    takenCareOf: one Boolean
}

abstract sig Authority {
    person: Person
}

sig MunicipalAuthority extends Authority{}

sig Policeman extends Authority{}

sig Ticket{
    compilation:  Segnalation -> one Policeman
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
                            s1.vehicle.plate = s2.vehicle.plate /*vicinity condition*/
                             /*time condition*/
}
