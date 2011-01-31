-- DROP TABLE "facilities" CASCADE;
-- DROP TABLE "features"   CASCADE;
-- DROP TABLE "meanings"   CASCADE ;

CREATE TABLE "facilities" (
    facility text NOT NULL,
    categorie text NOT NULL
);

CREATE TABLE "features" (
    facility text NOT NULL,
    feature text NOT NULL
);

CREATE TABLE "meanings" (
    feature text NOT NULL,
    meaning text NOT NULL
);

INSERT INTO "facilities" (facility, categorie) VALUES ('SQL', 'QLA');
INSERT INTO "facilities" (facility, categorie) VALUES ('ODBC', 'API');
INSERT INTO "facilities" (facility, categorie) VALUES ('LINQ', 'LIN');
INSERT INTO "facilities" (facility, categorie) VALUES ('Links', 'LIN');
INSERT INTO "facilities" (facility, categorie) VALUES ('Rails', 'ORM');
INSERT INTO "facilities" (facility, categorie) VALUES ('Ferry', 'LIB');
INSERT INTO "facilities" (facility, categorie) VALUES ('Kleisli', 'QLA');
INSERT INTO "facilities" (facility, categorie) VALUES ('ADO.NET', 'ORM');
INSERT INTO "facilities" (facility, categorie) VALUES ('HaskellDB', 'LIB');

INSERT INTO "features" (facility, feature) VALUES ('Kleisli', 'nest');
INSERT INTO "features" (facility, feature) VALUES ('Kleisli', 'comp');
INSERT INTO "features" (facility, feature) VALUES ('Kleisli', 'type');
INSERT INTO "features" (facility, feature) VALUES ('Links', 'comp');
INSERT INTO "features" (facility, feature) VALUES ('Links', 'type');
INSERT INTO "features" (facility, feature) VALUES ('Links', 'SQL');
INSERT INTO "features" (facility, feature) VALUES ('LINQ', 'nest');
INSERT INTO "features" (facility, feature) VALUES ('LINQ', 'comp');
INSERT INTO "features" (facility, feature) VALUES ('LINQ', 'type');
INSERT INTO "features" (facility, feature) VALUES ('HaskellDB', 'comp');
INSERT INTO "features" (facility, feature) VALUES ('HaskellDB', 'type');
INSERT INTO "features" (facility, feature) VALUES ('HaskellDB', 'SQL');
INSERT INTO "features" (facility, feature) VALUES ('SQL', 'aval');
INSERT INTO "features" (facility, feature) VALUES ('SQL', 'type');
INSERT INTO "features" (facility, feature) VALUES ('SQL', 'SQL');
INSERT INTO "features" (facility, feature) VALUES ('Rails', 'nest');
INSERT INTO "features" (facility, feature) VALUES ('Rails', 'maps');
INSERT INTO "features" (facility, feature) VALUES ('ADO.NET', 'maps');
INSERT INTO "features" (facility, feature) VALUES ('ADO.NET', 'comp');
INSERT INTO "features" (facility, feature) VALUES ('ADO.NET', 'type');
INSERT INTO "features" (facility, feature) VALUES ('Ferry', 'list');
INSERT INTO "features" (facility, feature) VALUES ('Ferry', 'nest');
INSERT INTO "features" (facility, feature) VALUES ('Ferry', 'comp');
INSERT INTO "features" (facility, feature) VALUES ('Ferry', 'aval');
INSERT INTO "features" (facility, feature) VALUES ('Ferry', 'type');
INSERT INTO "features" (facility, feature) VALUES ('Ferry', 'SQL');

INSERT INTO "meanings" (feature, meaning) VALUES ('maps', 'admits user-defined object mappings');
INSERT INTO "meanings" (feature, meaning) VALUES ('list', 'respects list order');
INSERT INTO "meanings" (feature, meaning) VALUES ('nest', 'supports data nesting');
INSERT INTO "meanings" (feature, meaning) VALUES ('comp', 'has compositional syntax and semantics');
INSERT INTO "meanings" (feature, meaning) VALUES ('aval', 'avoids query avalanches');
INSERT INTO "meanings" (feature, meaning) VALUES ('type', 'is statically type-checked');
INSERT INTO "meanings" (feature, meaning) VALUES ('SQL', 'guarantees translation to SQL');

ALTER TABLE ONLY "facilities"
    ADD CONSTRAINT "facilities_pkey" PRIMARY KEY (facility);

ALTER TABLE ONLY "features"
    ADD CONSTRAINT "features_pkey" PRIMARY KEY (facility, feature);

ALTER TABLE ONLY "meanings"
    ADD CONSTRAINT "meanings_pkey" PRIMARY KEY (feature);

ALTER TABLE ONLY "features"
    ADD CONSTRAINT "foreign facility" FOREIGN KEY (facility) REFERENCES "facilities"(facility);

ALTER TABLE ONLY "features"
    ADD CONSTRAINT "foreign feature" FOREIGN KEY (feature) REFERENCES "meanings"(feature);