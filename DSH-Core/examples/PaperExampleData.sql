CREATE TABLE "Facilities" (
    facility text NOT NULL,
    categorie text NOT NULL
);

CREATE TABLE "Features" (
    facility text NOT NULL,
    feature text NOT NULL
);

CREATE TABLE "Meanings" (
    feature text NOT NULL,
    meaning text NOT NULL
);

INSERT INTO "Facilities" (facility, categorie) VALUES ('SQL', 'QLA');
INSERT INTO "Facilities" (facility, categorie) VALUES ('ODBC', 'API');
INSERT INTO "Facilities" (facility, categorie) VALUES ('LINQ', 'LIN');
INSERT INTO "Facilities" (facility, categorie) VALUES ('Links', 'LIN');
INSERT INTO "Facilities" (facility, categorie) VALUES ('Rails', 'ORM');
INSERT INTO "Facilities" (facility, categorie) VALUES ('Ferry', 'LIB');
INSERT INTO "Facilities" (facility, categorie) VALUES ('Kleisli', 'QLA');
INSERT INTO "Facilities" (facility, categorie) VALUES ('ADO.NET', 'ORM');
INSERT INTO "Facilities" (facility, categorie) VALUES ('HaskellDB', 'LIB');

INSERT INTO "Features" (facility, feature) VALUES ('Kleisli', 'nest');
INSERT INTO "Features" (facility, feature) VALUES ('Kleisli', 'comp');
INSERT INTO "Features" (facility, feature) VALUES ('Kleisli', 'type');
INSERT INTO "Features" (facility, feature) VALUES ('Links', 'comp');
INSERT INTO "Features" (facility, feature) VALUES ('Links', 'type');
INSERT INTO "Features" (facility, feature) VALUES ('Links', 'SQL');
INSERT INTO "Features" (facility, feature) VALUES ('LINQ', 'nest');
INSERT INTO "Features" (facility, feature) VALUES ('LINQ', 'comp');
INSERT INTO "Features" (facility, feature) VALUES ('LINQ', 'type');
INSERT INTO "Features" (facility, feature) VALUES ('HaskellDB', 'comp');
INSERT INTO "Features" (facility, feature) VALUES ('HaskellDB', 'type');
INSERT INTO "Features" (facility, feature) VALUES ('HaskellDB', 'SQL');
INSERT INTO "Features" (facility, feature) VALUES ('SQL', 'aval');
INSERT INTO "Features" (facility, feature) VALUES ('SQL', 'type');
INSERT INTO "Features" (facility, feature) VALUES ('SQL', 'SQL');
INSERT INTO "Features" (facility, feature) VALUES ('Rails', 'nest');
INSERT INTO "Features" (facility, feature) VALUES ('Rails', 'maps');
INSERT INTO "Features" (facility, feature) VALUES ('ADO.NET', 'maps');
INSERT INTO "Features" (facility, feature) VALUES ('ADO.NET', 'comp');
INSERT INTO "Features" (facility, feature) VALUES ('ADO.NET', 'type');
INSERT INTO "Features" (facility, feature) VALUES ('Ferry', 'list');
INSERT INTO "Features" (facility, feature) VALUES ('Ferry', 'nest');
INSERT INTO "Features" (facility, feature) VALUES ('Ferry', 'comp');
INSERT INTO "Features" (facility, feature) VALUES ('Ferry', 'aval');
INSERT INTO "Features" (facility, feature) VALUES ('Ferry', 'type');
INSERT INTO "Features" (facility, feature) VALUES ('Ferry', 'SQL');


INSERT INTO "Meanings" (feature, meaning) VALUES ('maps', 'admits user-defined object mappings');
INSERT INTO "Meanings" (feature, meaning) VALUES ('list', 'respects list order');
INSERT INTO "Meanings" (feature, meaning) VALUES ('nest', 'supports data nesting');
INSERT INTO "Meanings" (feature, meaning) VALUES ('comp', 'has compositional syntax and semantics');
INSERT INTO "Meanings" (feature, meaning) VALUES ('aval', 'avoids query avalanches');
INSERT INTO "Meanings" (feature, meaning) VALUES ('type', 'is statically type-checked');
INSERT INTO "Meanings" (feature, meaning) VALUES ('SQL', 'guarantees translation to SQL');

ALTER TABLE ONLY "Facilities"
    ADD CONSTRAINT "Facilities_pkey" PRIMARY KEY (facility);

ALTER TABLE ONLY "Features"
    ADD CONSTRAINT "Features_pkey" PRIMARY KEY (facility, feature);

ALTER TABLE ONLY "Meanings"
    ADD CONSTRAINT "Meanings_pkey" PRIMARY KEY (feature);

ALTER TABLE ONLY "Features"
    ADD CONSTRAINT "foreign facility" FOREIGN KEY (facility) REFERENCES "Facilities"(facility);

ALTER TABLE ONLY "Features"
    ADD CONSTRAINT "foreign feature" FOREIGN KEY (feature) REFERENCES "Meanings"(feature);