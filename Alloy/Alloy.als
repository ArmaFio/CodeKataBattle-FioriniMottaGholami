abstract sig User {}

//Only Students can gain badges
sig Student extends User {
	gained: set Badge
}

//Educators can create or collaborate in a tournament
sig Educator extends User {
	creates: set Tournament,
   	collaboratesIn: set Tournament
}

//A Tournament has one creator who can optionally
//invite other Educators to collaborate, a list of available programming
//languages, and is structured in a set of battles
//The Tournament can start only when the number of students has excedeed the
//minParticipants value
//Each tournament has a list of associated badges which students can gain
//(rts= registration time slot)
sig Tournament {
    	creator : one Educator,
    	collaborators : set Educator,
	students: set Student,
	state: one State,
    	languages: some Language,
    	battles: set Battle,
	badges: set Badge,
   	rts: one TimeSlot,
	minParticipants: one Int
}{minParticipants > 0}

//Each battle consist in a coding challenge in one or more possible programming 
//languages, it's competed in teams, that have to find a solution to the exercise
//The Exercise is available for the students in the GitHub repository at repoLink
//and manual evaluation
//can be enabled to be performed at the end of the battle.
//maxTeamSize and minTeamSize are the constraints that Students have to respect 
//when forming a team about its size.
//(rts= registration time slot, sts = (solution) submission time slot)
sig Battle {

    	creator: one Educator,
	state: one State,
    	languages: some Language,
    	exercise: one Exercise,
	teams: some Team,
	repoLink: one RepoLink,
	rts: one TimeSlot,
	sts: one TimeSlot,
       manualEvaluation: one Int,
	maxTeamSize: one Int,
	minTeamSize: one Int
}{(manualEvaluation = 1 || manualEvaluation = 0) && minTeamSize >=1 && minTeamSize <= maxTeamSize && maxTeamSize >= 1}

//Each team is formed by one or more students and has a GitHub Fork when there
//is their solution which evaluated with a Score
sig Team {
   	members: some Student,
    	repo: lone Fork,
	score: lone Score
}

//The union of the files regarding the codekata: the text of the exercise and the 
//TestCases
sig Exercise {
    text: one Text,
    testCases: some TestCase
}

//The fork that a Team does from the codekata repo, identified by his link
//and containing team's solution
sig Fork{
	link: one Link,
	solution: lone Solution
}

//Gamification badge
sig Badge{}

//Team's solution code
sig Solution{}

//Team's solution evaluation
//A part of the score can be given manually by the educator
sig Score{
	automatic: one Automatic,
	manual: lone Manual,
}{}

//A TimeSlot: used for representing deadlines
sig TimeSlot{
	startTime: one DateTime,
	endTime: one DateTime
} {startTime != endTime} 

//Part of the score automatically assigned by Codescene
sig Automatic{}

//Part of the score manually assigned by the educator
sig Manual{}

sig DateTime{}
//Programming language 
sig Language{}

//Link of the code kata repo
sig RepoLink{}

//Test Cases for the codekata
sig TestCase{}

//a link
sig Link{}

//Text of the codakata problem
sig Text{}

//Possible states of a tournament or battle
//Ongoing battle or tournament has began but not ended yet
//Evaluating can only be reached by a battle if manual evaluation is enabled 
//Open represents the state when the subscription are opened, the tournament or
//battle hasn't began yet
//Closed represents the ended battle or tournament
abstract sig State{}
sig Opened extends State{}
sig Ongoing extends State{}
sig Evaluating extends State{}
sig Closed extends State{}

//FACTS

//Useful for the constraint to avoid inconsistencies in timeslot, two timeslots
//are different if completely disjointed
fact TimeSlotEqualityDefinition{
	all t1, t2: TimeSlot|
	t1!=t2 implies (t1.startTime!=t2.startTime and t1.endTime!=t2.endTime
	and t1.startTime!=t2.endTime and t1.endTime!=t2.startTime)
}

//If an educator creates a tournament then the tournament is set as created by 
//that educator
fact TournamentsCreatedBySameEducatorAreInEducatorList {
    all t: Tournament, e:Educator |
    	(t.creator=e implies t in e.creates) and 
	(e in t.collaborators implies t in e.collaboratesIn) and 
	(t in e.collaboratesIn implies e in t.collaborators) and 
	(t in e.creates implies t.creator=e)
}

//No inconsistencies in timeslots
fact DifferentTimeSlotsForTournamentAndBattles {
    all t: Tournament, b: Battle |
        b in t.battles implies (b.rts != t.rts and b.sts != t.rts and b.rts!=b.sts)
}


//tournament cannot have started if it hasn't reached the requested minimum number
//of participants
fact MinimumParticipantsConstraints {
	all t: Tournament |
		t.state = Ongoing implies #t.students >= t.minParticipants
}

//An Educator can't be a creator and a collaborator for the tournament at the same time
fact CreatorCantBeACollaborator{
	(all t: Tournament |
    		no e: Educator | e in t.collaborators and e = t.creator) &&
	(all e: Educator |
		no t: Tournament | t in e.creates and t in e.collaboratesIn) 
}

//One student can be part of only one team in a battle
fact NoDuplicateTeamMembersInBattle {
    all b: Battle, m: Student |
        (m in b.teams.members) implies (all t1, t2: Team | (t1 in b.teams and t2 in b.teams and t1 != t2) implies (m not in t1.members or m not in t2.members))
}

//A student has to have subscribed to the tournament to take part to a team for a battle
fact AllTeamMembersMustBeInTheTournament {
    all t: Team, to: Tournament |
        all m: t.members |
            m in to.students
        and
        t in to.battles.teams
}

//each team solution is evaluated separately
fact DifferentScoresForDifferentTeams{
	all disj t1,t2:Team| t1.score!=t2.score
}


//teams of a battle have to respect the size limits for the battle 
fact TeamSizeLimit {
	all t: Team, b: Battle| 
		t in b.teams implies #t.members >= b.minTeamSize and #t.members <= b.maxTeamSize
}


 
//A Battle cannot request the solution in a language which is not enabled for the tournament
fact LanguageAllowedInBattlesMustBeAllowedInTheTournament {
	all t: Tournament, b: Battle |
		b in t.battles implies b.languages in t.languages
}

//a battle can only be created in the context of a tournament
fact EachBattleAssociatedWithOneTournament {
    	all b: Battle |
        	one t: Tournament | b in t.battles

	all t: Tournament |
		t.state = Ongoing implies #t.battles >= 1
}

//Educator can and has only to manually evaluate all the solution if the manual evaluation
//is enabled 
fact ManualEvaluationRules {
    all b: Battle |
        (b.manualEvaluation = 0 implies
            all t: b.teams | t.score.manual = none
        ) and
        (b.manualEvaluation = 1 implies
            all t: b.teams |
                t.score != none implies t.score.manual != none
        )
}

//no team unlinked solution
fact EachSolutionBelongsToATeam {
    all f: Fork |
        one t: Team | f in t.repo
}

//two teams can't have the same repo
fact UniqueRepoLinks {
    all f1, f2: Fork |
        f1 != f2 implies f1.link != f2.link
}


//No unlinked badges
fact AllBadgesInsideTournaments{
	all b: Badge |
		one t: Tournament | b in t.badges
}

//No unlinked exercises
fact AllExercisesInsideBattle{
	all e: Exercise |
		one b: Battle | e in b.exercise
}

//a tournament can't host battles when it's opened (it has to be ongoing) and can't
//be closed without having hosted at least one battle
fact EachTournamentHasAtLeastOneBattle{
  	all t: Tournament |
    		t.state in Closed implies #t.battles >= 1 &&
    		t.state in Opened implies #t.battles = 0
}

//a tournament cannot assume the "Evaluating" state
fact NoTournamentsInEvaluating{
	all t:Tournament| not t.state in Evaluating
}

//no unlinked state
fact StateExistence {
    all s: State | s in Battle.state or s in Tournament.state
}

//no unlinked scores
fact ScoreExistence {
	all s: Score | s in Team.score
}

//no unlinked repolinks
fact RepoLinkExistence{
	all r: RepoLink| r in Battle.repoLink
}

//no unlinked manual scores
fact ManualExistence{
	all m:Manual| m in Score.manual
}

//no unlinked automatic scores
fact ManualExistence{
	all m:Automatic| m in Score.automatic
}

//no unlinked DateTimes
fact DateTimeExistence{
	all d:DateTime| d in TimeSlot.startTime or d in TimeSlot.endTime
}

//no unlinked Languages
fact LanguageExistence{
	all l: Language | l in Tournament.languages or l in Battle.languages
}

//no unlinked Testcases
fact TestCaseExistance {
	all t: TestCase | t in Exercise.testCases
}

//no unlinked teams
fact EachTeamIsInABattle{
	all t: Team |
		one b: Battle | t in b.teams
}

//no unlinked solutions
fact EachSolutionInAFork{
	all s: Solution |
		one f: Fork | s in f.solution
}

//no unlinked links
fact EachLinkInAFork{
	all l: Link |
		one f: Fork | l in f.link
}

//if a tournament is closed all his battles have to be closed
fact BattleStateConstraint{
	all b: Battle, t: Tournament |
		b in t.battles && t.state = Closed implies b.state = Closed
}

//if a battle is opened teams cannot have forked the repo at repoLink
//if manualevaluation is not enabled the battle never reaches evaluating state 
fact BattleStateConstraint {
    all b: Battle, t: b.teams |
        (b.state in Opened implies t.score = none and t.repo = none) and
        (b.state in Evaluating implies b.manualEvaluation = 1)
}

//if a team has submitted a solution it has to be evaluated
fact SolutionsAreEvaluated{
	all t:Team |
	t.repo.solution!=none implies t.score!=none
}

//If a student owns a badge of a tournament, the student must have joined the tournament
fact StudentOwnsBadgeInTournament {
    all s: Student, b: Badge |
        b in s.gained implies
            one t: Tournament | s in t.students and b in t.badges
}

//useful for avoiding score inconsistencies, scores are different if they are completely disjointed
fact ScoreInequalityDefinition{
	all disj s1,s2:Score | s1!=s2 implies (s1.manual!=s2.manual or s1.manual=none or s2.manual=none) and s1.automatic!=s2.automatic
}

//no unlinked Texts
fact Textexistence{
	all t:Text | t in Exercise.text
}


//Predicate
pred validTournamentInstance[t: Tournament] {
	#{t:Tournament| #t.collaborators=1}=1
    #{b:Battle | b.manualEvaluation=1&&b.maxTeamSize=2&&b.minTeamSize=2&&b.state in Ongoing}=1
    #Team=2
    #Fork=2 
    #Solution=2
    #Battle=1
    #Student=4
    #Language=2
}



// Example usage:
run validTournamentInstance for 6






