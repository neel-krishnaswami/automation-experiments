I have to groups of students taking different courses, and I have to
assign supervisors to each group, for each course. 

- Each supervisor rates their preference for each course on a 1-5
  scale, with 1 being least preferred and 5 being most preferred, and
  can supervise a certain number of hours each week.

- Each student group belongs to one of two years, 1A or 1B, and must
  have a supervisor for each of the courses they take. 

- There are 4 1B groups, and 3 1A groups. 

- The supervisor preferences are in supervisor-prefs.csv, listing for
  each supervisor their name, email, time zone, and for each course,
  what their rating is. The column names are in the first row, and the
  columns for the course names are prefixed with "1a-" or "1b-". 

- In each term, there are 8 weeks, so a supervisor offering 1 hour per
  week has 8 hours of supervision capacity in that term. 

- All of the courses have 4 1-hour supervisions per group per term,
  except for FHCI (2), Prolog (3), and CompNet (6).

- Minimum hours are a soft constraint (the minimums sum to more than
  the total demand), and having one supervisor take all the groups of
  a course is a soft preference.

- The "1b-L Semantics" column appears twice in supervisor-prefs.csv;
  take the max of the two ratings.

What are some good algorithm for assigning supervisors to groups?

