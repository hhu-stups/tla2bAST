MACHINE microwave
DEFINITIONS
 Init == (((magnetron_running = FALSE & door_open = FALSE) & button_locked = FALSE) & error = FALSE) & time = 0;
 Action_Start == (((((error = FALSE & magnetron_running = FALSE) & door_open = FALSE) & time /= 0) & magnetron_running_n = TRUE) & button_locked_n = TRUE) & TRUE = TRUE;
 Action_Stop == (((magnetron_running = TRUE & magnetron_running_n = FALSE) & button_locked_n = FALSE) & time_n = 0) & TRUE = TRUE;
 Door_Locked_When_Heating == (magnetron_running = TRUE => door_open = FALSE) & (magnetron_running = TRUE => button_locked = TRUE);
VARIABLES magnetron_running, door_open, button_locked, time, error
INVARIANT
((((magnetron_running : BOOL & door_open : BOOL) & button_locked : BOOL) & time : INTEGER) & error : BOOL) & Door_Locked_When_Heating
INITIALISATION
magnetron_running, door_open, button_locked, time, error:(Init)
OPERATIONS
 Action_Open_Door = SELECT (((button_locked = FALSE & magnetron_running = FALSE) & door_open = FALSE) & TRUE = TRUE) & TRUE = TRUE THEN door_open := TRUE END;

 Action_Close_Door = SELECT (door_open = TRUE & TRUE = TRUE) & TRUE = TRUE THEN door_open := FALSE END;

 Action_Change_Time = ANY time_n WHERE ((magnetron_running = FALSE & time_n : INTEGER) & (((((((time = 180 & time_n = 120) or (time = 120 & time_n = 90)) or (time = 90 & time_n = 60)) or (time = 60 & time_n = 30)) or (time = 30 & time_n = 15)) or (time = 15 & time_n = 180)) or (time = 0 & time_n = 180))) & TRUE = TRUE THEN time := time_n END;

 Action_Button_S = ANY magnetron_running_n, door_open_n, button_locked_n, time_n, error_n WHERE ((((magnetron_running_n : BOOL & door_open_n : BOOL) & button_locked_n : BOOL) & time_n : INTEGER) & error_n : BOOL) & ((magnetron_running = FALSE => Action_Start) & (not(magnetron_running = FALSE) => Action_Stop)) THEN magnetron_running,door_open,button_locked,time,error := magnetron_running_n,door_open_n,button_locked_n,time_n,error_n END;

 Action_Error = BEGIN error,magnetron_running := TRUE,FALSE END;

 Action_Tick = ANY magnetron_running_n, door_open_n, button_locked_n, time_n, error_n WHERE (((((magnetron_running = TRUE & magnetron_running_n : BOOL) & door_open_n : BOOL) & button_locked_n : BOOL) & time_n : INTEGER) & error_n : BOOL) & ((time /= 1 => time_n = time - 1 & TRUE = TRUE) & (not(time /= 1) => ((time_n = 0 & magnetron_running_n = FALSE) & button_locked_n = FALSE) & TRUE = TRUE)) THEN magnetron_running,door_open,button_locked,time,error := magnetron_running_n,door_open_n,button_locked_n,time_n,error_n END
END