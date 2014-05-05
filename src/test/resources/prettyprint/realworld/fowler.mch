MACHINE fowler
DEFINITIONS
 Init == (((state = "idle" & light = "off") & draw = "closed") & door = "unlocked") & panel = "locked";
VARIABLES state, light, draw, panel, door
INVARIANT
(((state : STRING & light : STRING) & draw : STRING) & panel : STRING) & door : STRING
INITIALISATION
state, light, draw, panel, door:(Init)
OPERATIONS
 CloseDoor = SELECT (door = "unlocked" & TRUE = TRUE) & TRUE = TRUE THEN door,state := "locked","active" END;

 LightOn = ANY state_n, panel_n, door_n WHERE ((((light = "off" & state_n : STRING) & panel_n : STRING) & door_n : STRING) & ((draw = "opened" => (state_n = "unlockedPanel" & panel_n = "unlocked") & door_n = "locked") & (not(draw = "opened") => state_n = "waitingForDraw" & TRUE = TRUE))) & TRUE = TRUE THEN light,state,panel,door := "on",state_n,panel_n,door_n END;

 OpenDraw = ANY state_n, panel_n, door_n WHERE ((((draw = "closed" & state_n : STRING) & panel_n : STRING) & door_n : STRING) & ((light = "on" => (state_n = "unlockedPanel" & panel_n = "unlocked") & door_n = "locked") & (not(light = "on") => state_n = "waitingForLight" & TRUE = TRUE))) & TRUE = TRUE THEN draw,state,panel,door := "opened",state_n,panel_n,door_n END;

 ClosePanel = SELECT panel = "unlocked" THEN panel,light,draw,door,state := "locked","off","closed","unlocked","idle" END
END