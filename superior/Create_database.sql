CREATE TABLE `type` (
  `id` int NOT NULL AUTO_INCREMENT,
  `name` varchar(255) NOT NULL,
  PRIMARY KEY (`id`)
);

CREATE TABLE `election` (
  `id` bigint NOT NULL AUTO_INCREMENT,
  `name` varchar(255) NOT NULL,
  `description` varchar(255) NOT NULL,
  `public` tinyint(1) NOT NULL,
  `end_when_all_voted` tinyint(1) NOT NULL,
  `type_id` int NOT NULL,
  `end` datetime NOT NULL,
  `result` varchar(255) NOT NULL DEFAULT 'none',
  `admin_token` varchar(25) NOT NULL,
  `admin_mail` varchar(255) NOT NULL,
  `parameter` varchar(5) NOT NULL DEFAULT '',
  PRIMARY KEY (`id`),
  UNIQUE KEY `uq_admin_token` (`admin_token`),
  KEY `type_id` (`type_id`),
  CONSTRAINT `election_ibfk_1` FOREIGN KEY (`type_id`) REFERENCES `type` (`id`)
);

CREATE TABLE `vote` (
  `id` bigint NOT NULL AUTO_INCREMENT,
  `value` varchar(255) NOT NULL,
  `election_id` bigint NOT NULL,
  PRIMARY KEY (`id`),
  KEY `fk_vote_election` (`election_id`),
  CONSTRAINT `fk_vote_election` FOREIGN KEY (`election_id`) REFERENCES `election` (`id`) ON DELETE CASCADE
);

CREATE TABLE `voter` (
  `id` bigint NOT NULL AUTO_INCREMENT,
  `mail` varchar(255) NOT NULL,
  `token` varchar(30) NOT NULL,
  `voted` tinyint(1) DEFAULT '0',
  `reminder_sent` tinyint(1) NOT NULL DEFAULT '0',
  `election_id` bigint NOT NULL,
  PRIMARY KEY (`id`),
  UNIQUE KEY `token` (`token`),
  KEY `fk_voter_election` (`election_id`),
  CONSTRAINT `fk_voter_election` FOREIGN KEY (`election_id`) REFERENCES `election` (`id`) ON DELETE CASCADE
);

CREATE TABLE `candidate` (
  `id` bigint NOT NULL AUTO_INCREMENT,
  `name` varchar(255) NOT NULL,
  `election_id` bigint NOT NULL,
  PRIMARY KEY (`id`),
  KEY `fk_candidate_election` (`election_id`),
  CONSTRAINT `fk_candidate_election` FOREIGN KEY (`election_id`) REFERENCES `election` (`id`) ON DELETE CASCADE
);
