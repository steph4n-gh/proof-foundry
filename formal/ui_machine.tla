--------------------------- MODULE ui_machine ---------------------------
EXTENDS FiniteSets, Naturals

CONSTANTS
    CheckMissionSeq,
    CheckDossierSeq,
    PreserveHealthyStream,
    ClearCrossMissionOverlay

Missions == {"m1", "m2"}
Claims == {"c1", "c2"}
Modes == {"live", "static"}
Views == {"missions", "control"}
None == "none"
MaxMissionSeq == 2
MaxDossierSeq == 2

VARIABLES
    transportStatus,
    mode,
    reqSeq,
    activeMission,
    inFlightMissions,
    routeView,
    routeMission,
    routeClaim,
    overlayKind,
    overlayClaim,
    overlayMission,
    overlayStatus,
    overlayReqSeq,
    dossierSeq,
    inFlightDossiers,
    monitor

vars == <<
    transportStatus, mode, reqSeq, activeMission, inFlightMissions,
    routeView, routeMission, routeClaim,
    overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq,
    dossierSeq, inFlightDossiers, monitor
>>

IdleMonitor == [
    kind |-> "idle",
    mission |-> None,
    tStatus |-> "boot",
    rMission |-> "m1",
    oStatus |-> None
]

Init ==
    /\ transportStatus = "boot"
    /\ mode = "unknown"
    /\ reqSeq = 0
    /\ activeMission = None
    /\ inFlightMissions = {}
    /\ routeView = "missions"
    /\ routeMission = "m1"
    /\ routeClaim = None
    /\ overlayKind = None
    /\ overlayClaim = None
    /\ overlayMission = None
    /\ overlayStatus = None
    /\ overlayReqSeq = 0
    /\ dossierSeq = 0
    /\ inFlightDossiers = {}
    /\ monitor = IdleMonitor

ResetOverlay ==
    /\ overlayKind' = None
    /\ overlayClaim' = None
    /\ overlayMission' = None
    /\ overlayStatus' = None
    /\ overlayReqSeq' = 0

KeepOverlay ==
    UNCHANGED <<overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq>>

CatalogLoaded(m) ==
    /\ transportStatus = "boot"
    /\ mode' = m
    /\ transportStatus' = IF m = "static" THEN "static_loading" ELSE "live_connecting"
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq,
                   dossierSeq, inFlightDossiers>>

CatalogFailed ==
    /\ transportStatus = "boot"
    /\ transportStatus' = "error"
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<mode, reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq,
                   dossierSeq, inFlightDossiers>>

MissionRequested(m) ==
    /\ transportStatus \notin {"boot", "error"}
    /\ reqSeq < MaxMissionSeq
    /\ reqSeq' = reqSeq + 1
    /\ inFlightMissions' = inFlightMissions \cup {<<reqSeq + 1, m>>}
    /\ transportStatus' =
        IF activeMission = None
        THEN (IF mode = "static" THEN "static_loading" ELSE "live_connecting")
        ELSE transportStatus
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<mode, activeMission,
                   routeView, routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq,
                   dossierSeq, inFlightDossiers>>

MissionLoaded(seq, m) ==
    /\ <<seq, m>> \in inFlightMissions
    /\ inFlightMissions' = inFlightMissions \ {<<seq, m>>}
    /\ IF ~CheckMissionSeq \/ seq = reqSeq
       THEN /\ activeMission' = m
            /\ transportStatus' = IF mode = "static" THEN "static_ready" ELSE "live_connecting"
            /\ routeMission' = m
            /\ routeClaim' = None
            /\ IF ClearCrossMissionOverlay
                  /\ overlayKind \in {"dossier", "attempt"}
                  /\ overlayMission # None
                  /\ overlayMission # m
               THEN ResetOverlay
               ELSE KeepOverlay
            /\ monitor' =
                IF seq # reqSeq
                THEN [IdleMonitor EXCEPT
                        !.kind = "stale_mission",
                        !.mission = activeMission,
                        !.tStatus = transportStatus,
                        !.rMission = routeMission]
                ELSE [IdleMonitor EXCEPT !.kind = "mission_commit"]
       ELSE /\ monitor' = [IdleMonitor EXCEPT
                    !.kind = "stale_mission",
                    !.mission = activeMission,
                    !.tStatus = transportStatus,
                    !.rMission = routeMission]
            /\ UNCHANGED <<transportStatus, activeMission, routeMission, routeClaim>>
            /\ KeepOverlay
    /\ UNCHANGED <<mode, reqSeq, routeView, dossierSeq, inFlightDossiers>>

MissionFailed(seq, m) ==
    /\ <<seq, m>> \in inFlightMissions
    /\ inFlightMissions' = inFlightMissions \ {<<seq, m>>}
    /\ IF ~CheckMissionSeq \/ seq = reqSeq
       THEN /\ transportStatus' =
                IF PreserveHealthyStream /\ activeMission # None
                THEN transportStatus
                ELSE "error"
       ELSE /\ UNCHANGED transportStatus
    /\ monitor' =
        IF seq # reqSeq
        THEN [IdleMonitor EXCEPT
                !.kind = "stale_mission",
                !.mission = activeMission,
                !.tStatus = transportStatus,
                !.rMission = routeMission]
        ELSE IdleMonitor
    /\ UNCHANGED <<mode, reqSeq, activeMission,
                   routeView, routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq,
                   dossierSeq, inFlightDossiers>>

SseOpen(m) ==
    /\ activeMission # None
    /\ transportStatus' =
        IF mode = "live" /\ m = activeMission
        THEN "live_connected"
        ELSE transportStatus
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<mode, reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq,
                   dossierSeq, inFlightDossiers>>

SseError(m) ==
    /\ activeMission # None
    /\ transportStatus' =
        IF mode = "live" /\ m = activeMission
        THEN "live_reconnecting"
        ELSE transportStatus
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<mode, reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq,
                   dossierSeq, inFlightDossiers>>

Retry ==
    /\ transportStatus = "error"
    /\ transportStatus' = "boot"
    /\ mode' = IF activeMission # None THEN mode ELSE "unknown"
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq,
                   dossierSeq, inFlightDossiers>>

OpenDossier(c, m) ==
    /\ transportStatus \notin {"boot", "error"}
    /\ dossierSeq < MaxDossierSeq
    /\ dossierSeq' = dossierSeq + 1
    /\ inFlightDossiers' = inFlightDossiers \cup {dossierSeq + 1}
    /\ overlayKind' = "dossier"
    /\ overlayClaim' = c
    /\ overlayMission' = m
    /\ overlayStatus' = "loading"
    /\ overlayReqSeq' = dossierSeq + 1
    /\ routeClaim' = IF m = routeMission THEN c ELSE None
    /\ monitor' = [IdleMonitor EXCEPT !.kind = "open_dossier"]
    /\ UNCHANGED <<transportStatus, mode, reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission>>

DossierLoaded(seq) ==
    /\ seq \in inFlightDossiers
    /\ inFlightDossiers' = inFlightDossiers \ {seq}
    /\ IF overlayKind = "dossier" /\ (~CheckDossierSeq \/ seq = overlayReqSeq)
       THEN overlayStatus' = "ready"
       ELSE UNCHANGED overlayStatus
    /\ monitor' =
        IF overlayKind = "dossier" /\ seq # overlayReqSeq
        THEN [IdleMonitor EXCEPT !.kind = "stale_dossier", !.oStatus = overlayStatus]
        ELSE IdleMonitor
    /\ UNCHANGED <<transportStatus, mode, reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayReqSeq, dossierSeq>>

DossierFailed(seq) ==
    /\ seq \in inFlightDossiers
    /\ inFlightDossiers' = inFlightDossiers \ {seq}
    /\ IF overlayKind = "dossier" /\ (~CheckDossierSeq \/ seq = overlayReqSeq)
       THEN overlayStatus' = "error"
       ELSE UNCHANGED overlayStatus
    /\ monitor' =
        IF overlayKind = "dossier" /\ seq # overlayReqSeq
        THEN [IdleMonitor EXCEPT !.kind = "stale_dossier", !.oStatus = overlayStatus]
        ELSE IdleMonitor
    /\ UNCHANGED <<transportStatus, mode, reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayReqSeq, dossierSeq>>

OpenAttempt(c, m) ==
    /\ transportStatus \notin {"boot", "error"}
    /\ overlayKind' = "attempt"
    /\ overlayClaim' = c
    /\ overlayMission' = m
    /\ overlayStatus' = None
    /\ overlayReqSeq' = 0
    /\ routeClaim' = None
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<transportStatus, mode, reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, dossierSeq, inFlightDossiers>>

OpenSearch ==
    /\ overlayKind' = "search"
    /\ overlayClaim' = None
    /\ overlayMission' = None
    /\ overlayStatus' = None
    /\ overlayReqSeq' = 0
    /\ routeClaim' = None
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<transportStatus, mode, reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, dossierSeq, inFlightDossiers>>

CloseOverlay ==
    /\ overlayKind # None
    /\ ResetOverlay
    /\ routeClaim' = None
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<transportStatus, mode, reqSeq, activeMission, inFlightMissions,
                   routeView, routeMission, dossierSeq, inFlightDossiers>>

RouteNavigate(v) ==
    /\ routeView # v
    /\ routeView' = v
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<transportStatus, mode, reqSeq, activeMission, inFlightMissions,
                   routeMission, routeClaim,
                   overlayKind, overlayClaim, overlayMission, overlayStatus, overlayReqSeq,
                   dossierSeq, inFlightDossiers>>

RouteSync(v) ==
    /\ routeView' = v
    /\ routeClaim' = None
    /\ IF overlayKind = "dossier" THEN ResetOverlay ELSE KeepOverlay
    /\ monitor' = IdleMonitor
    /\ UNCHANGED <<transportStatus, mode, reqSeq, activeMission, inFlightMissions,
                   routeMission, dossierSeq, inFlightDossiers>>

Done ==
    /\ reqSeq = MaxMissionSeq
    /\ dossierSeq = MaxDossierSeq
    /\ inFlightMissions = {}
    /\ inFlightDossiers = {}
    /\ UNCHANGED vars

Next ==
    \/ (\E m \in Modes : CatalogLoaded(m))
    \/ CatalogFailed
    \/ (\E m \in Missions : MissionRequested(m))
    \/ (\E seq \in 1..MaxMissionSeq, m \in Missions : MissionLoaded(seq, m))
    \/ (\E seq \in 1..MaxMissionSeq, m \in Missions : MissionFailed(seq, m))
    \/ (\E m \in Missions : SseOpen(m))
    \/ (\E m \in Missions : SseError(m))
    \/ Retry
    \/ (\E c \in Claims, m \in Missions : OpenDossier(c, m))
    \/ (\E seq \in 1..MaxDossierSeq : DossierLoaded(seq))
    \/ (\E seq \in 1..MaxDossierSeq : DossierFailed(seq))
    \/ (\E c \in Claims, m \in Missions : OpenAttempt(c, m))
    \/ OpenSearch
    \/ CloseOverlay
    \/ (\E v \in Views : RouteNavigate(v))
    \/ (\E v \in Views : RouteSync(v))
    \/ Done

SingleOverlayKind ==
    /\ overlayKind \in {None, "dossier", "attempt", "search"}
    /\ (overlayKind # "dossier" => (overlayStatus = None /\ overlayReqSeq = 0))
    /\ (overlayKind = "dossier" =>
        /\ overlayClaim \in Claims
        /\ overlayMission \in Missions
        /\ overlayStatus \in {"loading", "ready", "error"}
        /\ overlayReqSeq \in 1..MaxDossierSeq
        /\ overlayReqSeq <= dossierSeq)
    /\ (overlayKind = "attempt" =>
        /\ overlayClaim \in Claims
        /\ overlayMission \in Missions)
    /\ (overlayKind \in {None, "search"} =>
        /\ overlayClaim = None
        /\ overlayMission = None)

HealthyStreamSurvivesFailedSwitch ==
    activeMission # None => transportStatus # "error"

RouteMissionTracksActiveMission ==
    activeMission # None => routeMission = activeMission

NoCrossMissionOverlayAfterCommit ==
    (monitor.kind = "mission_commit"
     /\ activeMission # None
     /\ overlayKind \in {"dossier", "attempt"}
     /\ overlayMission # None)
        => overlayMission = activeMission

StaleMissionResponseIgnored ==
    monitor.kind = "stale_mission" =>
        /\ activeMission = monitor.mission
        /\ transportStatus = monitor.tStatus
        /\ routeMission = monitor.rMission

StaleDossierResponseIgnored ==
    monitor.kind = "stale_dossier" =>
        overlayStatus = monitor.oStatus

DossierRouteClaimSync ==
    /\ (overlayKind \in {None, "attempt", "search"} => routeClaim = None)
    /\ (monitor.kind = "open_dossier" =>
        routeClaim = (IF overlayMission = None \/ overlayMission = routeMission
                      THEN overlayClaim
                      ELSE None))
=============================================================================
