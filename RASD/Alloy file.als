
sig UsrId{}
abstract sig User{
    usrId: one UsrId
}
sig RegularUser extends User{
    trackedAreas: set Area
}
abstract sig Authority extends User{}
sig Policeman extends Authority{
    consideredReports: set Report
}
sig MunicipalAuthority extends Authority{
    trackedAreas: set Area,
    trackedUsers: set RegularUser,
    trackedPlates: set Plate
}
sig Position{}
sig Time{}
abstract sig ViolationType{}
sig ExpiredParking extends ViolationType{}
sig UnlawfulParking extends ViolationType{}
sig Plate{}
sig Photo{}
sig Intervention{}
sig Violation{
    violationType: one ViolationType,
    time: one Time,
    position: one Position,
    photo: one Photo,
    recognisedPlate: one Plate,//plate from photo
    writtenPlate: one Plate
}
sig Report{
    violation: one Violation,
    author: one User,
    dispatchedOfficer: lone Policeman,
    officerWhoTookAction: lone Policeman
}
sig Ticket{
    report: one Report,
    policeOfficer: one Policeman,
    recipient: one Plate
}
sig Area{
    reports: set Report,
    interventions: set Intervention
}

//facts
fact noSameOrDoubleID{
    no disj u1, u2: User |u1.usrId=u2.usrId  
}


fact needSamePlate{
    all v: Violation| v.recognisedPlate=v.writtenPlate
}

fact noDoublePhoto{
    no disj v1, v2: Violation| v1.photo=v2.photo
}

//In the application there should be a margin of tolerance in regards of the GPS location as well as in 
//regards of the time of the report,but in order to build and analyze the model in a simplier way these 
//margins of tolerance have been ignored
fact multipleReportsForOneInfraction{
    all disj r1, r2: Report| r1.violation.time=r2.violation.time and 
    r1.violation.violationType=r2.violation.violationType and r1.violation.position=r2.violation.position
     and r1.violation.writtenPlate=r2.violation.writtenPlate and r1.violation.recognisedPlate=r2.violation.recognisedPlate
     iff (r1.dispatchedOfficer=r2.dispatchedOfficer and r1.officerWhoTookAction=r2.officerWhoTookAction 
     and r1.author!=r2.author)
}

fact platesOnlyFromReports{
    all p: Plate| p in Report.violation.recognisedPlate
}

fact photosOnlyFromReports{
    all p: Photo| p in Report.violation.photo
}

fact noViolationWithoutReport{
    all v: Violation| v in Report.violation
}

fact allPsitionsFromReports{
    all p: Position| p in Report.violation.position
}

fact onlyConsiderReportsUndispatchedFor{
    all p: Policeman| all r: Report| r in p.consideredReports iff #r.dispatchedOfficer=0
}

fact sameOfficer{
    all r: Report| #r.officerWhoTookAction=1 iff ( #r.dispatchedOfficer=1 and 
    #r.dispatchedOfficer=#r.officerWhoTookAction)
}

fact ticketAuthor{
    all t: Ticket| t.policeOfficer=t.report.officerWhoTookAction
}

fact noDoubleTicket{
    no disj t1, t2: Ticket| t1.report=t2.report
}

fact noMunicipalAuthorityOnTheStreets{
    no m: MunicipalAuthority| m in Report.author
}

fact reportFromOfficer{
    all r:Report| r.author in Policeman iff r.dispatchedOfficer=r.author and r.officerWhoTookAction=r.author 
}

fact rightPersonBilled{
    all t: Ticket| t.recipient=t.report.violation.recognisedPlate
}

fact interventionsInArea{
    all a: Area| #a.interventions>0 implies #a.reports>0
}

fact baseCityArea{
    all r:Report| r in Area.reports
}

fact allInterventionsAboutSomeArea{
    all i: Intervention| i in Area.interventions
}

fact onlyVehiclesInTheDB{
    all m: MunicipalAuthority| m.trackedPlates in Violation.recognisedPlate
}



//G1
assert allReportsHaveOnePhoto{
    all r: Report| #r.violation.photo=1
}
//G2
assert allowDataMining{
    all ru: RegularUser| all ma: MunicipalAuthority|
    #ru.trackedAreas>=0 and #ma.trackedAreas>=0 and #ma.trackedUsers>=0 and #ma.trackedPlates>=0
}
//G3
assert plateRecognition{
    all r: Report| r.violation.writtenPlate=r.violation.recognisedPlate
}
//G4
assert locationPinpointing{
    all r: Report| #r.violation.position=1
}
//GA1.2
assert possibleInterventions{
    all a: Area| #a.interventions>=0 
}
//GA2.1
assert policemanWork{
    all p: Policeman| #p.consideredReports>=0
}
//GA2.3
assert takenCareOf{
    all r: Report| (r in Ticket.report iff #r.officerWhoTookAction=1) and #r.officerWhoTookAction=1 
    implies #r.dispatchedOfficer=1
}
//GA2.4
assert noSuchTicket{
    no t: Ticket| t.recipient!=t.report.violation.recognisedPlate
}


check allReportsHaveOnePhoto for 6
check allowDataMining for 6
check plateRecognition for 6
check locationPinpointing for 6
check possibleInterventions for 6
check policemanWork for 6
check takenCareOf for 6
check noSuchTicket for 6

pred world{
    #Plate>1
    #Report>=2
    #Ticket>=1
    #Policeman>=1
    #Violation>=2
    #User>2
    #ExpiredParking=1
    #UnlawfulParking=1
    #MunicipalAuthority>0  
    one r:Report| one a: Area| #a.interventions>0 and  r.author not in Policeman and #r.dispatchedOfficer=1
}


run world for 6