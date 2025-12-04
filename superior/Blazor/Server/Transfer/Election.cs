// Formally verified E-Voting using Dafny
// Copyright (C) 2025 Authors Superior Group
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// See the GNU Affero General Public License for more details.
// You should have received a copy of the GNU Affero General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

namespace E_Voting.Transfer
{
    public class Election
    {
        private long id;
        private string name;
        private string description;
        private bool public_election;
        private bool end_when_all_voted;
        private int type_id;
        private DateTime end;
        private string result;
        private string admin_token;
        private string admin_mail;
        private string parameter;
        private List<Candidate> candidates;
        private List<Voter> voters;
        private List<Vote> votes;

        public long ID => id;
        public string Name => name;
        public string Description => description;
        public DateTime End => end;
        public bool PublicElection => public_election;
        public bool EndWhenAllVoted => end_when_all_voted;
        public int TypeID => type_id;
        public string Result => result;
        public List<Candidate> Candidates => candidates;
        public List<Voter> Voters => voters;
        public List<Vote> Votes => votes;
        public string AdminMail => admin_mail;
        public string AdminToken => admin_token;
        public string Parameter => parameter;

        public Election(long id, string name, string description, DateTime end, bool public_election, bool end_when_all_voted, int type_id, string result, string admin_token, string admin_mail, string parameter)
        {
            this.id = id;
            this.name = name;
            this.description = description;
            this.end = end;
            this.public_election = public_election;
            this.end_when_all_voted = end_when_all_voted;
            this.type_id = type_id;
            this.result = result;
            this.admin_token = admin_token;
            this.admin_mail = admin_mail;
            this.parameter = parameter;

            candidates = new List<Candidate>();
            voters = new List<Voter>();
            votes = new List<Vote>();
        }

        public void AddCandidate(Candidate candidate)
        {
            candidates.Add(candidate);
        }

        public void AddVoter(Voter voter)
        {
            voters.Add(voter);
        }

        public void AddVote(Vote vote)
        {
            votes.Add(vote);
        }
    }
}
